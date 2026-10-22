-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:07:26.220081+00:00
-- url     : https://prove2.me/submissions/c59bf2f0-cbc8-43ae-873f-9643adf325f0

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal


open Filter Topology Matrix

namespace SROLP

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The restriction of the generator map to a finite set of indices. -/
noncomputable def resMap (g : ι → E) (S : Finset ι) : (S → ℝ) →ₗ[ℝ] E :=
  Fintype.linearCombination ℝ (fun i : S => g i)

theorem resMap_apply (g : ι → E) (S : Finset ι) (m : S → ℝ) :
    resMap g S m = ∑ i : S, m i • g i := by
  simp [resMap, Fintype.linearCombination_apply]

/-- Extension by zero of a function on `S`. -/
noncomputable def extZ (S : Finset ι) (m : S → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ S then m ⟨i, h⟩ else 0

theorem sum_extZ (g : ι → E) (S : Finset ι) (m : S → ℝ) :
    ∑ i, extZ S m i • g i = ∑ i : S, m i • g i := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [extZ, hi])]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extZ, i.2]

/-- Conic Carathéodory: every nonnegative combination is a nonnegative combination of a
linearly independent subfamily. -/
theorem caratheodory (g : ι → E) :
    ∀ (n : ℕ) (l : ι → ℝ), 0 ≤ l → (Finset.univ.filter (fun i => l i ≠ 0)).card = n →
      ∃ S : Finset ι, LinearMap.ker (resMap g S) = ⊥ ∧
        ∃ m : S → ℝ, 0 ≤ m ∧ resMap g S m = ∑ i, l i • g i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hcard
  set S := Finset.univ.filter (fun i => l i ≠ 0) with hS
  by_cases hker : LinearMap.ker (resMap g S) = ⊥
  · refine ⟨S, hker, fun i => l i, fun i => hl i, ?_⟩
    rw [resMap_apply]
    have : extZ S (fun i : S => l i) = l := by
      funext i
      by_cases hi : i ∈ S
      · simp [extZ, hi]
      · simp only [extZ, hi, dite_false]
        simp [hS] at hi
        exact hi.symm
    conv_rhs => rw [← this]
    rw [sum_extZ]
  · -- a nontrivial dependency among the generators on the support
    obtain ⟨μ0, hμ0, hne⟩ : ∃ μ0 : S → ℝ, resMap g S μ0 = 0 ∧ μ0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hker
      rw [LinearMap.ker_eq_bot']
      exact hcon
    -- make some coefficient positive
    obtain ⟨μ, hμ, hpos⟩ : ∃ μ : S → ℝ, resMap g S μ = 0 ∧ ∃ i, 0 < μ i := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      rcases lt_or_gt_of_ne hi with h | h
      · refine ⟨-μ0, by rw [map_neg, hμ0, neg_zero], i, ?_⟩
        simp only [Pi.neg_apply, Pi.zero_apply] at h ⊢
        linarith
      · exact ⟨μ0, hμ0, i, h⟩
    set μ' := extZ S μ with hμ'
    have hsumμ : ∑ i, μ' i • g i = 0 := by rw [hμ', sum_extZ, ← resMap_apply, hμ]
    set T := Finset.univ.filter (fun i => 0 < μ' i) with hT
    have hTne : T.Nonempty := by
      obtain ⟨i, hi⟩ := hpos
      refine ⟨i, ?_⟩
      simp [hT, hμ', extZ, i.2, hi]
    obtain ⟨i0, hi0T, hi0min⟩ := T.exists_min_image (fun i => l i / μ' i) hTne
    have hi0pos : 0 < μ' i0 := by simpa [hT] using hi0T
    set t := l i0 / μ' i0 with ht
    have ht0 : 0 ≤ t := div_nonneg (hl i0) hi0pos.le
    set l' : ι → ℝ := fun i => l i - t * μ' i with hl'
    have hl'0 : 0 ≤ l' := by
      intro i
      simp only [hl', Pi.zero_apply]
      by_cases hi : 0 < μ' i
      · have h1 : t ≤ l i / μ' i := hi0min i (by simp [hT, hi])
        have h2 : t * μ' i ≤ l i := by rwa [le_div_iff₀ hi] at h1
        linarith
      · push Not at hi
        have h1 : 0 ≤ l i := hl i
        nlinarith [mul_nonneg ht0 (neg_nonneg.2 hi)]
    have hsum' : ∑ i, l' i • g i = ∑ i, l i • g i := by
      simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hsumμ,
        smul_zero, sub_zero]
    -- the support strictly shrinks
    have hsub : Finset.univ.filter (fun i => l' i ≠ 0) ⊂ S := by
      refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i0, ?_, ?_⟩
      · intro i hi
        rw [hS]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hli
        apply hi
        have : μ' i = 0 := by
          simp only [hμ', extZ]
          have : i ∉ S := by simp [hS, hli]
          simp [this]
        simp [hl', hli, this]
      · have : μ' i0 ≠ 0 := hi0pos.ne'
        have hi0S : i0 ∈ S := by
          by_contra h
          apply this
          simp [hμ', extZ, h]
        exact hi0S
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, hl', ht]
        field_simp
        ring
    have hlt := Finset.card_lt_card hsub
    obtain ⟨S', hker', m, hm, heq⟩ := ih _ (hcard ▸ hlt) l' hl'0 rfl
    exact ⟨S', hker', m, hm, heq.trans hsum'⟩

/-- A finitely generated convex cone in a finite-dimensional space is closed. -/
theorem isClosed_cone (g : ι → E) :
    IsClosed {x : E | ∃ l : ι → ℝ, 0 ≤ l ∧ ∑ i, l i • g i = x} := by
  have hset : {x : E | ∃ l : ι → ℝ, 0 ≤ l ∧ ∑ i, l i • g i = x} =
      ⋃ S ∈ {S : Finset ι | LinearMap.ker (resMap g S) = ⊥},
        (resMap g S) '' {m : S → ℝ | 0 ≤ m} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨S, hS, m, hm, heq⟩ := caratheodory g _ l hl rfl
      exact ⟨S, hS, m, hm, heq⟩
    · rintro ⟨S, -, m, hm, rfl⟩
      refine ⟨extZ S m, fun i => ?_, ?_⟩
      · by_cases hi : i ∈ S
        · simpa [extZ, hi] using hm ⟨i, hi⟩
        · simp [extZ, hi]
      · rw [sum_extZ, resMap_apply]
  rw [hset]
  refine (Set.toFinite _).isClosed_biUnion fun S hS => ?_
  exact (LinearMap.isClosedEmbedding_of_injective hS).isClosedMap _
    (isClosed_le continuous_const continuous_id)

section LP

variable {κ : Type*} [Fintype κ]

theorem weak_duality (A : Matrix ι κ ℝ) (b : ι → ℝ) (q : κ → ℝ) {δ : ι → ℝ} {y : κ → ℝ}
    (hδ : Aᵀ *ᵥ δ = q ∧ 0 ≤ δ) (hy : b ≤ A *ᵥ y) : δ ⬝ᵥ b ≤ q ⬝ᵥ y := by
  have h1 : δ ⬝ᵥ b ≤ δ ⬝ᵥ (A *ᵥ y) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hδ.2 i)
  rw [dotProduct_mulVec, ← mulVec_transpose, hδ.1] at h1
  exact h1

/-- **Farkas' lemma** (inequality form): if `A y ≥ b` has no solution, there is a nonnegative
`l` with `Aᵀ l = 0` and `lᵀ b > 0`. -/
theorem farkas_ineq (A : Matrix ι κ ℝ) (b : ι → ℝ) (h : ¬ ∃ y : κ → ℝ, b ≤ A *ᵥ y) :
    ∃ l : ι → ℝ, 0 ≤ l ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b := by
  classical
  let g : ι → (κ → ℝ) × ℝ := fun i => (A i, b i)
  set K := {x : (κ → ℝ) × ℝ | ∃ l : ι → ℝ, 0 ≤ l ∧ ∑ i, l i • g i = x} with hK
  have hfst : ∀ l : ι → ℝ, (∑ i, l i • g i).1 = Aᵀ *ᵥ l := by
    intro l
    rw [Prod.fst_sum]
    funext k
    simp [g, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hsnd : ∀ l : ι → ℝ, (∑ i, l i • g i).2 = l ⬝ᵥ b := by
    intro l
    rw [Prod.snd_sum]
    simp [g, dotProduct]
  by_cases hx : ((0 : κ → ℝ), (1 : ℝ)) ∈ K
  · obtain ⟨l, hl, heq⟩ := hx
    refine ⟨l, hl, ?_, ?_⟩
    · rw [← hfst, heq]
    · rw [← hsnd, heq]; norm_num
  · exfalso
    have hconv : Convex ℝ K := by
      rintro _ ⟨l1, hl1, rfl⟩ _ ⟨l2, hl2, rfl⟩ a c ha hc _
      refine ⟨a • l1 + c • l2, ?_, ?_⟩
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact add_nonneg (mul_nonneg ha (hl1 i)) (mul_nonneg hc (hl2 i))
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, Finset.smul_sum]
    obtain ⟨f, u, hfK, hfx⟩ := geometric_hahn_banach_closed_point hconv (isClosed_cone g) hx
    have h0 : (0 : (κ → ℝ) × ℝ) ∈ K := ⟨0, le_rfl, by simp⟩
    have hu : 0 < u := by simpa using hfK 0 h0
    have hgi : ∀ i, f (g i) ≤ 0 := by
      intro i
      by_contra hpos
      push Not at hpos
      set c : ℝ := u / f (g i) + 1 with hc
      have hc0 : 0 ≤ c := by positivity
      have hmem : c • g i ∈ K := by
        refine ⟨fun j => if j = i then c else 0, ?_, ?_⟩
        · intro j; simp only [Pi.zero_apply]; split_ifs <;> simp [hc0]
        · simp [ite_smul, Finset.sum_ite_eq']
      have := hfK _ hmem
      rw [map_smul, smul_eq_mul, hc, add_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    set τ := f ((0 : κ → ℝ), (1 : ℝ)) with hτ
    have hτpos : 0 < τ := lt_trans hu hfx
    let e : κ → ℝ := fun k => f ((fun j => if k = j then 1 else 0), 0)
    have hlin : ∀ v : κ → ℝ, f (v, 0) = ∑ k, v k * e k := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ
        ((f : (κ → ℝ) × ℝ →L[ℝ] ℝ).toLinearMap.comp (LinearMap.inl ℝ (κ → ℝ) ℝ)) v
      simpa [e, smul_eq_mul] using this
    have hsplit : ∀ i, f (g i) = f (A i, 0) + b i * τ := by
      intro i
      have : g i = (A i, 0) + b i • ((0 : κ → ℝ), (1 : ℝ)) := by simp [g]
      rw [this, map_add, map_smul, smul_eq_mul]
    apply h
    refine ⟨fun k => -(e k) / τ, fun i => ?_⟩
    have h1 := hgi i
    rw [hsplit, hlin] at h1
    simp only [mulVec, dotProduct]
    have : ∑ k, A i k * (-(e k) / τ) = -(∑ k, A i k * e k) / τ := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, le_div_iff₀ hτpos]
    linarith

/-- LP strong duality, upper-bound direction: if `A y ≥ b` is feasible and every dual-feasible
`δ` has `δᵀ b ≤ t`, then some primal-feasible `y` has `qᵀ y ≤ t`. -/
theorem lp_upper (A : Matrix ι κ ℝ) (b : ι → ℝ) (q : κ → ℝ) (t : ℝ)
    (hfeas : ∃ y, b ≤ A *ᵥ y)
    (hdual : ∀ δ : ι → ℝ, Aᵀ *ᵥ δ = q ∧ 0 ≤ δ → δ ⬝ᵥ b ≤ t) :
    ∃ y, b ≤ A *ᵥ y ∧ q ⬝ᵥ y ≤ t := by
  by_contra hno
  push Not at hno
  let A' : Matrix (Option ι) κ ℝ := fun o k => match o with
    | none => -q k
    | some i => A i k
  let b' : Option ι → ℝ := fun o => match o with
    | none => -t
    | some i => b i
  have eA1 : ∀ k, A' none k = -q k := fun _ => rfl
  have eA2 : ∀ i k, A' (some i) k = A i k := fun _ _ => rfl
  have eb1 : b' none = -t := rfl
  have eb2 : ∀ i, b' (some i) = b i := fun _ => rfl
  have hinf : ¬ ∃ y : κ → ℝ, b' ≤ A' *ᵥ y := by
    rintro ⟨y, hy⟩
    have h1 : b ≤ A *ᵥ y := fun i => by
      have := hy (some i)
      simpa only [eb2, mulVec, dotProduct, eA2] using this
    have h2 := hy none
    simp only [eb1, mulVec, dotProduct, eA1] at h2
    have h3 := hno y h1
    simp only [dotProduct, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h2
    simp only [dotProduct] at h3
    linarith
  obtain ⟨l, hl, hAl, hlb⟩ := farkas_ineq A' b' hinf
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = l none := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ι → ℝ, lam = fun i => l (some i) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := fun i => by rw [hlam]; exact hl (some i)
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact hl none
  have hA : Aᵀ *ᵥ lam = μ • q := by
    funext k
    have := congrFun hAl k
    simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_option, eA1, eA2,
      Pi.zero_apply] at this
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul, hlam, hμ]
    linarith
  have hb : lam ⬝ᵥ b - μ * t > 0 := by
    simp only [dotProduct, Fintype.sum_option, eb1, eb2] at hlb
    simp only [dotProduct, hlam, hμ]
    linarith
  rcases hμ0.lt_or_eq with hμpos | hμz
  · have hd := hdual (μ⁻¹ • lam) ⟨?_, ?_⟩
    · have : (μ⁻¹ • lam) ⬝ᵥ b = μ⁻¹ * (lam ⬝ᵥ b) := by rw [smul_dotProduct, smul_eq_mul]
      rw [this, inv_mul_le_iff₀ hμpos] at hd
      linarith
    · rw [mulVec_smul, hA, smul_smul, inv_mul_cancel₀ hμpos.ne', one_smul]
    · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact mul_nonneg (inv_nonneg.2 hμ0) (hlam0 i)
  · obtain ⟨y0, hy0⟩ := hfeas
    have hA0 : Aᵀ *ᵥ lam = 0 := by rw [hA, ← hμz, zero_smul]
    have h1 := weak_duality A b 0 ⟨hA0, hlam0⟩ hy0
    rw [zero_dotProduct] at h1
    rw [← hμz, zero_mul, sub_zero] at hb
    linarith

/-- The standard-form polyhedron `D = {δ ≥ 0 : Wᵀ δ = q}`. -/
def stdPoly (W : Matrix ι κ ℝ) (q : κ → ℝ) : Set (ι → ℝ) := {δ | Wᵀ *ᵥ δ = q ∧ 0 ≤ δ}

/-- A direction inside `D` that strictly shrinks the support (used for the fundamental theorem
of LP). -/
theorem exists_extreme_ge (W : Matrix ι κ ℝ) (q : κ → ℝ) (b : ι → ℝ) (t : ℝ)
    (hbdd : ∀ δ ∈ stdPoly W q, δ ⬝ᵥ b ≤ t) :
    ∀ (n : ℕ) (δ : ι → ℝ), δ ∈ stdPoly W q →
      (Finset.univ.filter (fun i => δ i ≠ 0)).card = n →
      ∃ δ' ∈ Set.extremePoints ℝ (stdPoly W q), δ ⬝ᵥ b ≤ δ' ⬝ᵥ b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro δ hδ hcard
  by_cases hext : δ ∈ Set.extremePoints ℝ (stdPoly W q)
  · exact ⟨δ, hext, le_rfl⟩
  rw [mem_extremePoints] at hext
  push Not at hext
  obtain ⟨a, ha, c, hc, hseg, hneq⟩ := hext hδ
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
  have haδ : a ≠ δ := by
    intro h
    apply hneq h
    funext j
    have := congrFun hcomb j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [h] at this
    have h2 : β * c j = β * δ j := by linear_combination this - δ j * hαβ
    exact mul_left_cancel₀ hβ.ne' h2
  set w := a - δ with hw
  have hWw : Wᵀ *ᵥ w = 0 := by rw [hw, mulVec_sub, ha.1, hδ.1, sub_self]
  have hsupp : ∀ j, δ j = 0 → w j = 0 := by
    intro j hj
    have h1 : α * a j + β * c j = 0 := by
      have := congrFun hcomb j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, hj]
    have ha0 := ha.2 j
    have hc0 := hc.2 j
    have : a j = 0 := by
      have : α * a j = 0 := by nlinarith [mul_nonneg hβ.le hc0, mul_nonneg hα.le ha0]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hα.ne'
      · exact h
    simp [hw, this, hj]
  have hw0 : w ≠ 0 := sub_ne_zero.2 haδ
  -- a good direction `σ`
  obtain ⟨σ, hWσ, hsuppσ, hbσ, hneg⟩ : ∃ σ : ι → ℝ, Wᵀ *ᵥ σ = 0 ∧ (∀ j, δ j = 0 → σ j = 0) ∧
      0 ≤ σ ⬝ᵥ b ∧ ∃ j, σ j < 0 := by
    have hcases : ∀ σ : ι → ℝ, σ ≠ 0 → Wᵀ *ᵥ σ = 0 → (∀ j, δ j = 0 → σ j = 0) →
        0 ≤ σ ⬝ᵥ b → (∃ j, σ j < 0) ∨ (0 ≤ σ ∧ σ ⬝ᵥ b = 0) := by
      intro σ hσ0 hWσ hsσ hbσ
      by_cases hn : ∃ j, σ j < 0
      · exact Or.inl hn
      · push Not at hn
        right
        refine ⟨fun j => hn j, ?_⟩
        rcases hbσ.lt_or_eq with hpos | heq
        · exfalso
          -- unbounded ray inside `D`
          set s : ℝ := (t - δ ⬝ᵥ b) / (σ ⬝ᵥ b) + 1 with hs
          have hδb := hbdd δ hδ
          have hs0 : 0 ≤ s := by
            have : 0 ≤ (t - δ ⬝ᵥ b) / (σ ⬝ᵥ b) := div_nonneg (by linarith) hpos.le
            linarith
          have hmem : δ + s • σ ∈ stdPoly W q := by
            refine ⟨?_, fun j => ?_⟩
            · rw [mulVec_add, mulVec_smul, hWσ, smul_zero, add_zero, hδ.1]
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
              exact add_nonneg (hδ.2 j) (mul_nonneg hs0 (hn j))
          have := hbdd _ hmem
          rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hs, add_mul,
            div_mul_cancel₀ _ hpos.ne'] at this
          linarith
        · exact heq.symm
    rcases le_total 0 (w ⬝ᵥ b) with hb | hb
    · rcases hcases w hw0 hWw hsupp hb with h | ⟨hnn, hbz⟩
      · exact ⟨w, hWw, hsupp, hb, h⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
        refine ⟨-w, by rw [mulVec_neg, hWw, neg_zero], fun j hj => by simp [hsupp j hj],
          by rw [neg_dotProduct, hbz, neg_zero], j, ?_⟩
        have := hnn j
        simp only [Pi.neg_apply, Pi.zero_apply] at hj ⊢
        exact neg_neg_of_pos (lt_of_le_of_ne this (Ne.symm hj))
    · have hb' : 0 ≤ (-w) ⬝ᵥ b := by rw [neg_dotProduct]; linarith
      have hw0' : -w ≠ 0 := neg_ne_zero.2 hw0
      have hWw' : Wᵀ *ᵥ (-w) = 0 := by rw [mulVec_neg, hWw, neg_zero]
      have hsupp' : ∀ j, δ j = 0 → (-w) j = 0 := fun j hj => by simp [hsupp j hj]
      rcases hcases (-w) hw0' hWw' hsupp' hb' with h | ⟨hnn, hbz⟩
      · exact ⟨-w, hWw', hsupp', hb', h⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
        refine ⟨w, hWw, hsupp, ?_, j, ?_⟩
        · rw [neg_dotProduct] at hbz; linarith
        · have := hnn j
          simp only [Pi.neg_apply, Pi.zero_apply] at this hj
          rcases lt_or_gt_of_ne hj with h | h
          · exact h
          · linarith
  -- move along `σ` until a coordinate vanishes
  set T := Finset.univ.filter (fun j => σ j < 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hneg; exact ⟨j, by simp [hT, hj]⟩
  obtain ⟨j0, hj0T, hj0min⟩ := T.exists_min_image (fun j => δ j / (-σ j)) hTne
  have hj0neg : σ j0 < 0 := by simpa [hT] using hj0T
  set s := δ j0 / (-σ j0) with hs
  have hs0 : 0 ≤ s := div_nonneg (hδ.2 j0) (by linarith)
  set δ' := δ + s • σ with hδ'
  have hδ'mem : δ' ∈ stdPoly W q := by
    refine ⟨?_, fun j => ?_⟩
    · rw [hδ', mulVec_add, mulVec_smul, hWσ, smul_zero, add_zero, hδ.1]
    · simp only [hδ', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hj : σ j < 0
      · have h1 : s ≤ δ j / (-σ j) := hj0min j (by simp [hT, hj])
        have h2 : s * (-σ j) ≤ δ j := by rwa [le_div_iff₀ (by linarith)] at h1
        linarith
      · push Not at hj
        exact add_nonneg (hδ.2 j) (mul_nonneg hs0 hj)
  have hbδ' : δ ⬝ᵥ b ≤ δ' ⬝ᵥ b := by
    rw [hδ', add_dotProduct, smul_dotProduct, smul_eq_mul]
    nlinarith [mul_nonneg hs0 hbσ]
  have hsub : Finset.univ.filter (fun j => δ' j ≠ 0) ⊂ Finset.univ.filter (fun j => δ j ≠ 0) := by
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨j0, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro hδj
      apply hj
      simp [hδ', hδj, hsuppσ j hδj]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hδj
      have := hsuppσ j0 hδj
      linarith
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, hδ', Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hs]
      rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hj0neg.ne]
      ring
  have hlt := Finset.card_lt_card hsub
  obtain ⟨δ'', hδ''ext, hδ''b⟩ := ih _ (hcard ▸ hlt) δ' hδ'mem rfl
  exact ⟨δ'', hδ''ext, hbδ'.trans hδ''b⟩

/-- An extreme point of `D` is determined by (any superset of) its support. -/
theorem eq_of_support (W : Matrix ι κ ℝ) (q : κ → ℝ) {δ δ' : ι → ℝ}
    (hδ : δ ∈ Set.extremePoints ℝ (stdPoly W q)) (hδ' : δ' ∈ stdPoly W q)
    (hs : ∀ j, δ j = 0 → δ' j = 0) : δ' = δ := by
  obtain ⟨hD, hext⟩ := mem_extremePoints.1 hδ
  set w := δ' - δ with hw
  have hev : ∀ j, ∀ᶠ t in 𝓝[>] (0:ℝ), t * |w j| ≤ δ j := by
    intro j
    by_cases h0 : δ j = 0
    · have : w j = 0 := by simp [hw, hs j h0, h0]
      exact Filter.Eventually.of_forall fun t => by simp [this, h0]
    · have hpos : 0 < δ j := lt_of_le_of_ne (hD.2 j) (Ne.symm h0)
      have ht : Tendsto (fun t : ℝ => t * |w j|) (𝓝[>] 0) (𝓝 0) := by
        have h := (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (|w j|)
        simp only [id, zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (ht.eventually (gt_mem_nhds hpos)).mono fun t ht => ht.le
  obtain ⟨t, ht, htpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have htpos' : (0:ℝ) < t := htpos
  have mem : ∀ σ : ℝ, |σ| ≤ t → δ + σ • w ∈ stdPoly W q := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · rw [mulVec_add, mulVec_smul, hw, mulVec_sub, hδ'.1, hD.1]
      simp
    · intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have h1 := ht j
      have h2 : |σ * w j| ≤ t * |w j| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      have h3 := neg_abs_le (σ * w j)
      linarith
  have hseg : δ ∈ openSegment ℝ (δ + t • w) (δ + (-t) • w) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (hext _ (mem t (by rw [abs_of_pos htpos'])) _
    (mem (-t) (by rw [abs_neg, abs_of_pos htpos'])) hseg).1
  have hw0 : t • w = 0 := by
    have := congrArg (fun z => z - δ) this
    simpa using this
  have : w = 0 := by
    rcases smul_eq_zero.1 hw0 with h | h
    · exact absurd h htpos'.ne'
    · exact h
  rw [hw] at this
  exact sub_eq_zero.1 this

theorem extremePoints_finite (W : Matrix ι κ ℝ) (q : κ → ℝ) :
    (Set.extremePoints ℝ (stdPoly W q)).Finite := by
  let supp : (ι → ℝ) → Finset ι := fun δ => Finset.univ.filter (fun j => δ j ≠ 0)
  refine Set.Finite.of_finite_image (f := supp) (Set.toFinite _) ?_
  intro δ hδ δ' hδ' hsupp
  have h := eq_of_support W q hδ hδ'.1 (fun j hj => by
    by_contra hne
    have : j ∈ supp δ' := by simp [supp, hne]
    rw [← hsupp] at this
    simp [supp, hj] at this)
  exact h.symm

/-- Strong duality with an optimal dual vertex: if the primal `A y ≥ b` is feasible and the dual
polyhedron is nonempty, some vertex `δ` of the dual polyhedron and some primal-feasible `y` satisfy
`qᵀ y ≤ δᵀ b`. -/
theorem lp_vertex (A : Matrix ι κ ℝ) (b : ι → ℝ) (q : κ → ℝ)
    (hfeas : ∃ y, b ≤ A *ᵥ y) (hD : (stdPoly A q).Nonempty) :
    ∃ δ ∈ Set.extremePoints ℝ (stdPoly A q), ∃ y, b ≤ A *ᵥ y ∧ q ⬝ᵥ y ≤ δ ⬝ᵥ b := by
  obtain ⟨y0, hy0⟩ := hfeas
  have hbdd : ∀ δ ∈ stdPoly A q, δ ⬝ᵥ b ≤ q ⬝ᵥ y0 := fun δ hδ => weak_duality A b q hδ hy0
  obtain ⟨δ1, hδ1⟩ := hD
  obtain ⟨e, he, -⟩ := exists_extreme_ge A q b _ hbdd _ δ1 hδ1 rfl
  obtain ⟨δs, hδs, hmax⟩ := Set.exists_max_image _ (fun δ => δ ⬝ᵥ b)
    (extremePoints_finite A q) ⟨e, he⟩
  refine ⟨δs, hδs, lp_upper A b q _ ⟨y0, hy0⟩ fun δ hδ => ?_⟩
  obtain ⟨δ', hδ', hle⟩ := exists_extreme_ge A q b _ hbdd _ δ hδ rfl
  exact hle.trans (hmax δ' hδ')

end LP

end SROLP

namespace SROMeasAux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- The second-stage cost `ζ ↦ Q(x, ζ)` is Borel measurable: its strict sublevel sets are
projections of σ-compact sets. -/
theorem measurable_Q (M : Model n d r m mt) (x : Fin n → ℝ) : Measurable (fun ζ => Q M x ζ) := by
  refine measurable_of_Iio fun t => ?_
  let F : Set ((Fin d → ℝ) × (Fin r → ℝ)) := {z | M.h z.1 ≤ M.T *ᵥ x + M.W *ᵥ z.2}
  have hF : IsClosed F := by
    refine isClosed_le ?_ ?_
    · unfold Model.h
      exact continuous_const.add (continuous_const.matrix_mulVec continuous_fst)
    · exact continuous_const.add (continuous_const.matrix_mulVec continuous_snd)
  let K : ℚ → Set ((Fin d → ℝ) × (Fin r → ℝ)) := fun k => F ∩ {z | M.q ⬝ᵥ z.2 ≤ (k : ℝ)}
  have hK : ∀ k, IsClosed (K k) := fun k =>
    hF.inter (isClosed_le (continuous_const.dotProduct continuous_snd) continuous_const)
  have hset : (fun ζ => Q M x ζ) ⁻¹' Set.Iio t =
      ⋃ (k : ℚ) (_ : (((k : ℝ)) : EReal) < t), Prod.fst '' K k := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · intro hQ
      unfold Q at hQ
      rw [sInf_lt_iff] at hQ
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := hQ
      obtain ⟨k, hk1, hk2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
      refine ⟨k, hk2, (ζ, y), ⟨hy, ?_⟩, rfl⟩
      exact_mod_cast hk1.le
    · rintro ⟨k, hk, ⟨ζ', y⟩, ⟨hy, hyk⟩, rfl⟩
      unfold Q
      refine lt_of_le_of_lt (sInf_le ⟨y, hy, rfl⟩) (lt_of_le_of_lt ?_ hk)
      exact_mod_cast hyk
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  refine measurableSet_of_isSigmaCompact ?_
  exact ((isSigmaCompact_univ.of_isClosed_subset (hK k) (Set.subset_univ _))).image
    continuous_fst

theorem toReal_eq_pos_sub_neg (x : EReal) :
    x.toReal = (x.toENNReal).toReal - ((-x).toENNReal).toReal := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top r),
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top (-r))]
    simp only [EReal.toReal_coe]
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    rcases le_total 0 r with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- Integrability of the second-stage cost at an optimal first-stage decision. -/
theorem Q_integrable (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) (xs : Fin n → ℝ) (v : ℝ)
    (hV : Vstar M μ xs = (v : EReal)) :
    Integrable (fun ζ => (Q M xs ζ).toReal) μ ∧
      ∫ ζ, (Q M xs ζ).toReal ∂μ = v - M.c ⬝ᵥ xs ∧
      ∀ᵐ ζ ∂μ, Q M xs ζ ≠ ⊤ ∧ Q M xs ζ ≠ ⊥ := by
  have hmeas := measurable_Q M xs
  set A := ∫⁻ ζ, (Q M xs ζ).toENNReal ∂μ with hA
  set B := ∫⁻ ζ, (-Q M xs ζ).toENNReal ∂μ with hB
  unfold Vstar DupacovaWets.Consistency.expect at hV
  rw [← hA, ← hB] at hV
  have hAfin : A ≠ ∞ := by
    intro h
    rw [if_pos h] at hV
    simp at hV
  rw [if_neg hAfin] at hV
  have hBfin : B ≠ ∞ := by
    intro h
    rw [h] at hV
    have : ((A : EReal) - ((⊤ : ℝ≥0∞) : EReal)) = ⊥ := by
      rw [EReal.coe_ennreal_top]
      exact EReal.sub_top _
    rw [this] at hV
    simp at hV
  have hpm : Measurable fun ζ => (Q M xs ζ).toENNReal := hmeas.ereal_toENNReal
  have hnm : Measurable fun ζ => (-Q M xs ζ).toENNReal := hmeas.neg.ereal_toENNReal
  have hpi : Integrable (fun ζ => ((Q M xs ζ).toENNReal).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hAfin
  have hni : Integrable (fun ζ => ((-Q M xs ζ).toENNReal).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hnm.aemeasurable hBfin
  have hfeq : (fun ζ => (Q M xs ζ).toReal) =
      fun ζ => ((Q M xs ζ).toENNReal).toReal - ((-Q M xs ζ).toENNReal).toReal :=
    funext fun ζ => toReal_eq_pos_sub_neg _
  have hpa : ∀ᵐ ζ ∂μ, (Q M xs ζ).toENNReal < ∞ := ae_lt_top hpm hAfin
  have hna : ∀ᵐ ζ ∂μ, (-Q M xs ζ).toENNReal < ∞ := ae_lt_top hnm hBfin
  refine ⟨hfeq ▸ hpi.sub hni, ?_, ?_⟩
  · rw [hfeq, integral_sub hpi hni, integral_toReal hpm.aemeasurable hpa,
      integral_toReal hnm.aemeasurable hna, ← hA, ← hB]
    have hA' : ((A : ℝ≥0∞) : EReal) = ((A.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hAfin]
    have hB' : ((B : ℝ≥0∞) : EReal) = ((B.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hBfin]
    rw [hA', hB', ← EReal.coe_sub, ← EReal.coe_add] at hV
    have := EReal.coe_eq_coe_iff.1 hV
    linarith
  · filter_upwards [hpa, hna] with ζ h1 h2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at h1; simp at h1
    · rw [h] at h2; simp at h2

end SROMeasAux

namespace SROL3Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

theorem dualNorm_bdd (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (v : Fin k → ℝ) :
    BddAbove ((fun u => u ⬝ᵥ v) '' {u : Fin k → ℝ | ‖WithLp.toLp p u‖ ≤ 1}) := by
  refine ⟨∑ i, |v i|, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  simp only [dotProduct]
  refine Finset.sum_le_sum fun i _ => ?_
  have hu' : ‖WithLp.toLp p u‖ ≤ 1 := hu
  have hui : |u i| ≤ 1 := by
    have := PiLp.norm_apply_le (WithLp.toLp p u) i
    simp only [Real.norm_eq_abs] at this
    linarith
  calc u i * v i ≤ |u i * v i| := le_abs_self _
    _ = |u i| * |v i| := abs_mul _ _
    _ ≤ 1 * |v i| := mul_le_mul_of_nonneg_right hui (abs_nonneg _)
    _ = |v i| := one_mul _

theorem dualNorm_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (v : Fin k → ℝ) :
    0 ≤ dualNorm p v := by
  unfold dualNorm
  refine le_csSup_of_le (dualNorm_bdd p v) ⟨0, ?_, rfl⟩ (by simp)
  simp

/-- Hölder's inequality for the dual norm. -/
theorem holder (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (u v : Fin k → ℝ) :
    u ⬝ᵥ v ≤ ‖WithLp.toLp p u‖ * dualNorm p v := by
  by_cases hu : ‖WithLp.toLp p u‖ = 0
  · have : u = 0 := by
      have h0 : WithLp.toLp p u = 0 := norm_eq_zero.1 hu
      have := congrArg WithLp.ofLp h0
      simpa using this
    simp [this]
  · have hpos : 0 < ‖WithLp.toLp p u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    set c := ‖WithLp.toLp p u‖ with hc
    have hmem : (c⁻¹ • u) ∈ {u : Fin k → ℝ | ‖WithLp.toLp p u‖ ≤ 1} := by
      show ‖WithLp.toLp p (c⁻¹ • u)‖ ≤ 1
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), ← hc,
        inv_mul_cancel₀ hpos.ne']
    have h1 : (c⁻¹ • u) ⬝ᵥ v ≤ dualNorm p v :=
      le_csSup (dualNorm_bdd p v) ⟨_, hmem, rfl⟩
    rw [smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ hpos] at h1
    exact h1

/-- Over `B(ẑ, ε)`, a linear function exceeds its value at `ẑ` by at most `ε‖a‖_*`. -/
theorem lin_ball_le (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (a zhat ζ : Fin k → ℝ) (ε : ℝ)
    (hζ : ‖WithLp.toLp p (ζ - zhat)‖ ≤ ε) :
    a ⬝ᵥ ζ ≤ a ⬝ᵥ zhat + ε * dualNorm p a := by
  have h := holder p (ζ - zhat) a
  rw [sub_dotProduct, dotProduct_comm ζ a, dotProduct_comm zhat a] at h
  have := mul_le_mul_of_nonneg_right hζ (dualNorm_nonneg p a)
  linarith

theorem dot_W (M : Model n d r m mt) {δ : Fin m → ℝ} (hδ : M.Wᵀ *ᵥ δ = M.q) (v : Fin r → ℝ) :
    δ ⬝ᵥ (M.W *ᵥ v) = M.q ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hδ]

theorem dot_transpose {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) (w : Fin k → ℝ) (ζ : Fin l → ℝ) :
    (Aᵀ *ᵥ w) ⬝ᵥ ζ = w ⬝ᵥ (A *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_mulVec]

end SROL3Aux

open TwoStageSRO.AsymOpt SROLP SROMeasAux SROL3Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (x : Fin n → ℝ) (C : Set (Matrix (Fin r) (Fin d) ℝ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hfeas : ∀ ζ ∈ XiStar M xs, QC M p C ε x ζ < ⊤) :
    ∀ ζ ∈ XiStar M xs,
      QC M p C ε x ζ ≤
        Q M xs ζ + (ε : EReal) * etaC M p C + ((Lconst M p * dualNorm p (x - xs) : ℝ) : EReal) := by
  classical
  intro zhat hzhat
  have hDdef : Ddual M = stdPoly M.W M.q := rfl
  -- Step 0: the dual polyhedron `D` is nonempty (footnote 3)
  have hD : (stdPoly M.W M.q).Nonempty := by
    have hVxs : Vstar M μ xs = vStar M μ :=
      le_antisymm (le_iInf fun x => hxs (Set.mem_univ x)) (iInf_le _ _)
    obtain ⟨v, hv⟩ : ∃ v : ℝ, vStar M μ = (v : EReal) :=
      ⟨(vStar M μ).toReal, (EReal.coe_toReal hA2.1 hA2.2.1).symm⟩
    obtain ⟨-, -, hfin⟩ := Q_integrable M μ xs v (hVxs.trans hv)
    haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
    obtain ⟨ζ0, hζ0top, hζ0bot⟩ := hfin.exists
    by_contra hDe
    rw [Set.not_nonempty_iff_eq_empty] at hDe
    obtain ⟨y1, hy1⟩ : ∃ y1 : Fin r → ℝ, M.h ζ0 ≤ M.T *ᵥ xs + M.W *ᵥ y1 := by
      by_contra hno
      push Not at hno
      apply hζ0top
      unfold Q
      rw [sInf_eq_top]
      rintro _ ⟨y, hy, rfl⟩
      exact absurd hy (hno y)
    apply hζ0bot
    rw [EReal.eq_bot_iff_forall_lt]
    intro t
    have hb : M.h ζ0 - M.T *ᵥ xs ≤ M.W *ᵥ y1 := by
      intro j; have := hy1 j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    obtain ⟨y, hy, hqy⟩ := lp_upper M.W (M.h ζ0 - M.T *ᵥ xs) M.q (t - 1) ⟨y1, hb⟩
      (fun δ hδ => by
        have : δ ∈ stdPoly M.W M.q := hδ
        rw [hDe] at this
        exact absurd this (Set.notMem_empty δ))
    have hyf : M.h ζ0 ≤ M.T *ᵥ xs + M.W *ᵥ y := by
      intro j; have := hy j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    unfold Q
    refine lt_of_le_of_lt (sInf_le ⟨y, hyf, rfl⟩) ?_
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  -- Step 1: a feasible linear rule `(ỹ⁰, Ỹ)` with `Ỹ ∈ C`
  have h1 := hfeas zhat hzhat
  unfold QC at h1
  rw [iInf_lt_iff] at h1
  obtain ⟨⟨y0t, Yt⟩, h1⟩ := h1
  rw [iInf_lt_iff] at h1
  obtain ⟨⟨hYC, hrob⟩, -⟩ := h1
  set S := ball p zhat ε ∩ Xi M with hS
  have hzS : zhat ∈ S := ⟨by show ‖WithLp.toLp p (zhat - zhat)‖ ≤ ε; simpa using hε, hzhat.1⟩
  -- Step 2: the robust right-hand side
  set a : Fin m → Fin d → ℝ := fun j => M.H j - Ytᵀ *ᵥ M.W j with ha
  have ha_eq : ∀ j ζ, a j ⬝ᵥ ζ = (M.H *ᵥ ζ) j - (M.W *ᵥ (Yt *ᵥ ζ)) j := by
    intro j ζ
    simp only [ha, sub_dotProduct, dot_transpose]
    rfl
  have hhold : ∀ j, ∀ ζ ∈ S, a j ⬝ᵥ ζ ≤ a j ⬝ᵥ zhat + ε * dualNorm p (a j) :=
    fun j ζ hζ => lin_ball_le p (a j) zhat ζ ε hζ.1
  have hbdd : ∀ j, BddAbove ((fun ζ => a j ⬝ᵥ ζ) '' S) := fun j =>
    ⟨_, by rintro _ ⟨ζ, hζ, rfl⟩; exact hhold j ζ hζ⟩
  set Mj : Fin m → ℝ := fun j => sSup ((fun ζ => a j ⬝ᵥ ζ) '' S) with hMj
  have hMj_ge : ∀ j, ∀ ζ ∈ S, a j ⬝ᵥ ζ ≤ Mj j := fun j ζ hζ =>
    le_csSup (hbdd j) ⟨ζ, hζ, rfl⟩
  have hMj_le : ∀ j, Mj j ≤ a j ⬝ᵥ zhat + ε * dualNorm p (a j) := fun j =>
    csSup_le ⟨_, zhat, hzS, rfl⟩ (by rintro _ ⟨ζ, hζ, rfl⟩; exact hhold j ζ hζ)
  set β : Fin m → ℝ := fun j => M.h0 j - (M.T *ᵥ x) j + Mj j with hβ
  have hfeasβ : β ≤ M.W *ᵥ y0t := by
    intro j
    have : Mj j ≤ (M.W *ᵥ y0t) j + (M.T *ᵥ x) j - M.h0 j := by
      refine csSup_le ⟨_, zhat, hzS, rfl⟩ ?_
      rintro _ ⟨ζ, hζ, rfl⟩
      have h := hrob ζ hζ j
      simp only [Model.h, Pi.add_apply, Matrix.mulVec_add] at h
      have := ha_eq j ζ
      simp only at this ⊢
      linarith
    simp only [hβ]
    linarith
  -- Step 3: strong duality with an optimal dual vertex
  obtain ⟨δ, hδext, y, hy, hqy⟩ := lp_vertex M.W β M.q ⟨y0t, hfeasβ⟩ hD
  have hδD : δ ∈ stdPoly M.W M.q := hδext.1
  -- the new rule `(y, Ỹ)` is robustly feasible
  have hrobNew : robFeas M x S (fun ζ => y + Yt *ᵥ ζ) := by
    intro ζ hζ j
    have h1 := hy j
    have h2 := hMj_ge j ζ hζ
    have h3 := ha_eq j ζ
    simp only [hβ] at h1
    simp only [Model.h, Pi.add_apply, Matrix.mulVec_add]
    linarith
  -- its worst-case cost
  have hcost : robCost M S (fun ζ => y + Yt *ᵥ ζ) ≤
      ((M.q ⬝ᵥ y + (Ytᵀ *ᵥ M.q) ⬝ᵥ zhat + ε * dualNorm p (Ytᵀ *ᵥ M.q) : ℝ) : EReal) := by
    unfold robCost
    refine iSup₂_le fun ζ hζ => EReal.coe_le_coe_iff.2 ?_
    have h := lin_ball_le p (Ytᵀ *ᵥ M.q) zhat ζ ε hζ.1
    rw [dot_transpose] at h
    rw [dotProduct_add]
    linarith
  have hQC : QC M p C ε x zhat ≤
      ((M.q ⬝ᵥ y + (Ytᵀ *ᵥ M.q) ⬝ᵥ zhat + ε * dualNorm p (Ytᵀ *ᵥ M.q) : ℝ) : EReal) := by
    unfold QC
    exact (iInf₂_le (y, Yt) ⟨hYC, hrobNew⟩).trans hcost
  -- Step 4: bound `qᵀ y ≤ δᵀ β`
  set E : ℝ := dualNorm p (Ytᵀ *ᵥ M.q) + ∑ j, δ j * dualNorm p (a j) with hE
  have hδβ : δ ⬝ᵥ β ≤ δ ⬝ᵥ (M.h zhat - M.T *ᵥ x) - (Ytᵀ *ᵥ M.q) ⬝ᵥ zhat +
      ε * ∑ j, δ j * dualNorm p (a j) := by
    have hsum : δ ⬝ᵥ β ≤ ∑ j, δ j * (M.h0 j - (M.T *ᵥ x) j + (a j ⬝ᵥ zhat +
        ε * dualNorm p (a j))) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hδD.2 j)
      simp only [hβ]
      linarith [hMj_le j]
    have hexp : ∑ j, δ j * (M.h0 j - (M.T *ᵥ x) j + (a j ⬝ᵥ zhat + ε * dualNorm p (a j))) =
        δ ⬝ᵥ (M.h zhat - M.T *ᵥ x) - δ ⬝ᵥ (M.W *ᵥ (Yt *ᵥ zhat)) +
          ε * ∑ j, δ j * dualNorm p (a j) := by
      simp only [ha_eq]
      simp only [Model.h, dotProduct, Pi.sub_apply, Pi.add_apply, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, dot_W M hδD.1, ← dot_transpose] at hsum
    exact hsum
  -- Step 5: compare with `x*`
  have hTδ : δ ⬝ᵥ (M.h zhat - M.T *ᵥ x) = δ ⬝ᵥ (M.h zhat - M.T *ᵥ xs) -
      (M.Tᵀ *ᵥ δ) ⬝ᵥ (x - xs) := by
    rw [dot_transpose, dotProduct_sub, dotProduct_sub, Matrix.mulVec_sub, dotProduct_sub]
    ring
  have hL : -((M.Tᵀ *ᵥ δ) ⬝ᵥ (x - xs)) ≤ Lconst M p * dualNorm p (x - xs) := by
    have h := holder p (-(M.Tᵀ *ᵥ δ)) (x - xs)
    rw [neg_dotProduct, WithLp.toLp_neg, norm_neg] at h
    have hLb : ‖WithLp.toLp p (M.Tᵀ *ᵥ δ)‖ ≤ Lconst M p := by
      unfold Lconst
      exact le_csSup ((extremePoints_finite M.W M.q).image _).bddAbove ⟨δ, hδext, rfl⟩
    have := mul_le_mul_of_nonneg_right hLb (dualNorm_nonneg p (x - xs))
    linarith
  have hweak : ((δ ⬝ᵥ (M.h zhat - M.T *ᵥ xs) : ℝ) : EReal) ≤ Q M xs zhat := by
    unfold Q
    refine le_sInf ?_
    rintro _ ⟨y', hy', rfl⟩
    refine EReal.coe_le_coe_iff.2 (weak_duality M.W _ M.q hδD ?_)
    intro j; have := hy' j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
  have hη : ((E : ℝ) : EReal) ≤ etaC M p C := by
    unfold etaC
    exact le_iSup₂_of_le Yt hYC (le_iSup₂_of_le δ hδext le_rfl)
  -- assemble
  have hreal : M.q ⬝ᵥ y + (Ytᵀ *ᵥ M.q) ⬝ᵥ zhat + ε * dualNorm p (Ytᵀ *ᵥ M.q) ≤
      δ ⬝ᵥ (M.h zhat - M.T *ᵥ xs) + ε * E + Lconst M p * dualNorm p (x - xs) := by
    rw [hE]
    linarith
  calc QC M p C ε x zhat
      ≤ ((δ ⬝ᵥ (M.h zhat - M.T *ᵥ xs) + ε * E + Lconst M p * dualNorm p (x - xs) : ℝ) :
          EReal) := hQC.trans (EReal.coe_le_coe_iff.2 hreal)
    _ = ((δ ⬝ᵥ (M.h zhat - M.T *ᵥ xs) : ℝ) : EReal) + (ε : EReal) * ((E : ℝ) : EReal) +
          ((Lconst M p * dualNorm p (x - xs) : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_add, EReal.coe_mul]
    _ ≤ Q M xs zhat + (ε : EReal) * etaC M p C +
          ((Lconst M p * dualNorm p (x - xs) : ℝ) : EReal) := by
        gcongr
