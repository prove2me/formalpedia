-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:24:34.336882+00:00
-- url     : https://prove2.me/submissions/46a44a11-535f-4aba-80bc-9035bc5bf700

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

section Hoffman

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- An infeasible system `A z ≥ b` has a uniformly positive violation. -/
theorem infeasible_gap (A : Matrix ι κ ℝ) (b : ι → ℝ) (h : ¬ ∃ z, b ≤ A *ᵥ z) :
    ∃ c : ℝ, 0 < c ∧ ∀ z0 : κ → ℝ, ∃ i, c ≤ b i - (A *ᵥ z0) i := by
  obtain ⟨l, hl, hAl, hlb⟩ := farkas_ineq A b h
  set S := ∑ i, l i with hS
  have hSpos : 0 < S := by
    rcases (Finset.sum_nonneg fun i _ => hl i : 0 ≤ S).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hl0 : ∀ i, l i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hl i)).1 h1.symm i
          (Finset.mem_univ i)
        exact this
      have : l ⬝ᵥ b = 0 := by simp [dotProduct, hl0]
      linarith
  refine ⟨l ⬝ᵥ b / S, div_pos hlb hSpos, fun z0 => ?_⟩
  by_contra hcon
  push Not at hcon
  have hzero : l ⬝ᵥ (A *ᵥ z0) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAl, zero_dotProduct]
  have hlt : ∑ i, l i * (b i - (A *ᵥ z0) i) < ∑ i, l i * (l ⬝ᵥ b / S) := by
    obtain ⟨i0, hi0⟩ : ∃ i0, 0 < l i0 := by
      by_contra hno
      push Not at hno
      have : ∀ i, l i = 0 := fun i => le_antisymm (hno i) (hl i)
      have : l ⬝ᵥ b = 0 := by simp [dotProduct, this]
      linarith
    refine Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hcon i).le (hl i))
      ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon i0) hi0⟩
  have e1 : ∑ i, l i * (b i - (A *ᵥ z0) i) = l ⬝ᵥ b := by
    have : ∑ i, l i * (b i - (A *ᵥ z0) i) = l ⬝ᵥ b - l ⬝ᵥ (A *ᵥ z0) := by
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [this, hzero, sub_zero]
  have e2 : ∑ i, l i * (l ⬝ᵥ b / S) = l ⬝ᵥ b := by
    rw [← Finset.sum_mul, ← hS, mul_div_cancel₀ _ hSpos.ne']
  linarith

/-- Rows of the auxiliary LP used for Hoffman's bound. -/
abbrev HRow (ι κ : Type*) := ι ⊕ (κ ⊕ (κ ⊕ Unit))

/-- The constraint matrix of `min t` s.t. `A z ≥ b`, `t ≥ |z_k - z0_k|`, `t ≥ 0`;
variables are `some k ↦ z k` and `none ↦ t`. -/
noncomputable def hMat (A : Matrix ι κ ℝ) : Matrix (HRow ι κ) (Option κ) ℝ :=
  fun row col => match row, col with
  | Sum.inl i, some k => A i k
  | Sum.inl _, none => 0
  | Sum.inr (Sum.inl k), some k' => if k' = k then -1 else 0
  | Sum.inr (Sum.inl _), none => 1
  | Sum.inr (Sum.inr (Sum.inl k)), some k' => if k' = k then 1 else 0
  | Sum.inr (Sum.inr (Sum.inl _)), none => 1
  | Sum.inr (Sum.inr (Sum.inr _)), some _ => 0
  | Sum.inr (Sum.inr (Sum.inr _)), none => 1

noncomputable def hRhs (b : ι → ℝ) (z0 : κ → ℝ) : HRow ι κ → ℝ :=
  fun row => match row with
  | Sum.inl i => b i
  | Sum.inr (Sum.inl k) => -z0 k
  | Sum.inr (Sum.inr (Sum.inl k)) => z0 k
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def hCost : Option κ → ℝ := fun o => match o with
  | none => 1
  | some _ => 0

theorem hMat_mulVec (A : Matrix ι κ ℝ) (w : Option κ → ℝ) :
    (∀ i, (hMat A *ᵥ w) (Sum.inl i) = (A *ᵥ fun k => w (some k)) i) ∧
    (∀ k, (hMat A *ᵥ w) (Sum.inr (Sum.inl k)) = w none - w (some k)) ∧
    (∀ k, (hMat A *ᵥ w) (Sum.inr (Sum.inr (Sum.inl k))) = w none + w (some k)) ∧
    (∀ u, (hMat A *ᵥ w) (Sum.inr (Sum.inr (Sum.inr u))) = w none) := by
  refine ⟨fun i => ?_, fun k => ?_, fun k => ?_, fun u => ?_⟩
  · simp [mulVec, dotProduct, Fintype.sum_option, hMat]
  · simp [mulVec, dotProduct, Fintype.sum_option, hMat, ite_mul, Finset.sum_ite_eq']
    try ring
  · simp [mulVec, dotProduct, Fintype.sum_option, hMat, ite_mul, Finset.sum_ite_eq']
    try ring
  · simp [mulVec, dotProduct, Fintype.sum_option, hMat]

/-- **Hoffman's error bound** (sup-norm form): for a nonempty polyhedron `{z : A z ≥ b}` there is
a constant `θ` such that any `z0` violating each constraint by at most `ρ` is within sup-distance
`θ ρ` of the polyhedron. -/
theorem hoffman (A : Matrix ι κ ℝ) (b : ι → ℝ) (hP : ∃ z, b ≤ A *ᵥ z) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ z0 : κ → ℝ, ∀ ρ : ℝ, 0 ≤ ρ → (∀ i, b i - (A *ᵥ z0) i ≤ ρ) →
      ∃ z, b ≤ A *ᵥ z ∧ ∀ k, |z k - z0 k| ≤ θ * ρ := by
  classical
  set A' := hMat A with hA'
  set D := stdPoly A' (hCost (κ := κ)) with hD
  have hfin := extremePoints_finite A' (hCost (κ := κ))
  set θ : ℝ := ∑ δ ∈ hfin.toFinset, ∑ i, δ (Sum.inl i) with hθ
  have hδnn : ∀ δ ∈ Set.extremePoints ℝ D, 0 ≤ ∑ i, δ (Sum.inl i) := fun δ hδ =>
    Finset.sum_nonneg fun i _ => hδ.1.2 (Sum.inl i)
  have hθ0 : 0 ≤ θ := Finset.sum_nonneg fun δ hδ => hδnn δ (hfin.mem_toFinset.1 hδ)
  refine ⟨θ, hθ0, fun z0 ρ hρ hviol => ?_⟩
  obtain ⟨z1, hz1⟩ := hP
  have hev := hMat_mulVec A
  -- a primal feasible point
  set w1 : Option κ → ℝ := fun o => match o with
    | none => ∑ k, |z1 k - z0 k|
    | some k => z1 k with hw1
  have hw1n : w1 none = ∑ k, |z1 k - z0 k| := rfl
  have hw1s : ∀ k, w1 (some k) = z1 k := fun _ => rfl
  have hfeas1 : hRhs b z0 ≤ A' *ᵥ w1 := by
    rintro (i | k | k | u)
    · rw [(hev w1).1 i]; exact hz1 i
    · rw [(hev w1).2.1 k]
      show -z0 k ≤ w1 none - w1 (some k)
      rw [hw1n, hw1s]
      have := Finset.single_le_sum (fun k _ => abs_nonneg (z1 k - z0 k)) (Finset.mem_univ k)
      have := le_abs_self (z1 k - z0 k)
      linarith
    · rw [(hev w1).2.2.1 k]
      show z0 k ≤ w1 none + w1 (some k)
      rw [hw1n, hw1s]
      have := Finset.single_le_sum (fun k _ => abs_nonneg (z1 k - z0 k)) (Finset.mem_univ k)
      have := neg_abs_le (z1 k - z0 k)
      linarith
    · rw [(hev w1).2.2.2 u]
      show (0:ℝ) ≤ w1 none
      rw [hw1n]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  -- the dual polyhedron is nonempty (the primal objective is bounded below by `0`)
  have hDne : D.Nonempty := by
    by_contra hDe
    rw [Set.not_nonempty_iff_eq_empty] at hDe
    obtain ⟨w, hw, hcw⟩ := lp_upper A' (hRhs b z0) hCost (-1) ⟨w1, hfeas1⟩
      (fun δ hδ => by
        have : δ ∈ D := hδ
        rw [hDe] at this
        exact absurd this (Set.notMem_empty δ))
    have h1 := hw (Sum.inr (Sum.inr (Sum.inr ())))
    rw [(hev w).2.2.2 ()] at h1
    simp only [hRhs] at h1
    have : hCost ⬝ᵥ w = w none := by simp [dotProduct, Fintype.sum_option, hCost]
    linarith
  obtain ⟨δ, hδext, w, hw, hcw⟩ := lp_vertex A' (hRhs b z0) hCost ⟨w1, hfeas1⟩ hDne
  have hδD : δ ∈ D := hδext.1
  -- bound the dual objective by the violation
  set w0 : Option κ → ℝ := fun o => match o with
    | none => 0
    | some k => z0 k with hw0
  have hdual : δ ⬝ᵥ hRhs b z0 ≤ (∑ i, δ (Sum.inl i)) * ρ := by
    have hsplit : δ ⬝ᵥ hRhs b z0 = δ ⬝ᵥ (A' *ᵥ w0) + δ ⬝ᵥ (hRhs b z0 - A' *ᵥ w0) := by
      rw [dotProduct_sub]; ring
    have hzero : δ ⬝ᵥ (A' *ᵥ w0) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hδD.1]
      simp [dotProduct, Fintype.sum_option, hCost, w0]
    rw [hsplit, hzero, zero_add]
    simp only [dotProduct, Fintype.sum_sum_type, Pi.sub_apply]
    have r2 : ∀ k, hRhs b z0 (Sum.inr (Sum.inl k)) - (A' *ᵥ w0) (Sum.inr (Sum.inl k)) = 0 := by
      intro k; rw [(hev w0).2.1 k]; simp [hRhs, w0]
    have r3 : ∀ k, hRhs b z0 (Sum.inr (Sum.inr (Sum.inl k))) -
        (A' *ᵥ w0) (Sum.inr (Sum.inr (Sum.inl k))) = 0 := by
      intro k; rw [(hev w0).2.2.1 k]; simp [hRhs, w0]
    have r4 : ∀ u, hRhs b z0 (Sum.inr (Sum.inr (Sum.inr u))) -
        (A' *ᵥ w0) (Sum.inr (Sum.inr (Sum.inr u))) = 0 := by
      intro u; rw [(hev w0).2.2.2 u]; simp [hRhs, w0]
    simp only [r2, r3, r4, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hδD.2 (Sum.inl i))
    rw [(hev w0).1 i]
    simpa [hRhs, w0] using hviol i
  have hθδ : ∑ i, δ (Sum.inl i) ≤ θ :=
    Finset.single_le_sum (f := fun δ => ∑ i, δ (Sum.inl i))
      (fun δ hδ => hδnn δ (hfin.mem_toFinset.1 hδ)) (hfin.mem_toFinset.2 hδext)
  have hcw' : hCost ⬝ᵥ w = w none := by simp [dotProduct, Fintype.sum_option, hCost]
  refine ⟨fun k => w (some k), fun i => ?_, fun k => ?_⟩
  · have := hw (Sum.inl i); rw [(hev w).1 i] at this; exact this
  · have h1 := hw (Sum.inr (Sum.inl k))
    have h2 := hw (Sum.inr (Sum.inr (Sum.inl k)))
    rw [(hev w).2.1 k] at h1
    rw [(hev w).2.2.1 k] at h2
    simp only [hRhs] at h1 h2
    have ht : w none ≤ θ * ρ := by
      calc w none = hCost ⬝ᵥ w := hcw'.symm
        _ ≤ δ ⬝ᵥ hRhs b z0 := hcw
        _ ≤ (∑ i, δ (Sum.inl i)) * ρ := hdual
        _ ≤ θ * ρ := mul_le_mul_of_nonneg_right hθδ hρ
    rw [abs_le]
    constructor <;> linarith

end Hoffman

end SROLP

namespace SROEq3Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

/-- The lifted system describing `{(ζ, y) : ζ ∈ Ξ, Tx* + Wy ≥ h(ζ), G_J ζ = g⁰_J}`. -/
noncomputable def liftMat (M : Model n d r m mt) (J : Finset (Fin mt)) :
    Matrix (Fin mt ⊕ (Fin m ⊕ Fin mt)) (Fin d ⊕ Fin r) ℝ :=
  fun row col => match row, col with
  | Sum.inl k, Sum.inl i => M.G k i
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr (Sum.inl j), Sum.inl i => -M.H j i
  | Sum.inr (Sum.inl j), Sum.inr l => M.W j l
  | Sum.inr (Sum.inr k), Sum.inl i => if k ∈ J then -M.G k i else 0
  | Sum.inr (Sum.inr _), Sum.inr _ => 0

noncomputable def liftRhs (M : Model n d r m mt) (xs : Fin n → ℝ) (J : Finset (Fin mt)) :
    Fin mt ⊕ (Fin m ⊕ Fin mt) → ℝ :=
  fun row => match row with
  | Sum.inl k => M.g0 k
  | Sum.inr (Sum.inl j) => M.h0 j - (M.T *ᵥ xs) j
  | Sum.inr (Sum.inr k) => if k ∈ J then -M.g0 k else 0

theorem liftMat_mulVec (M : Model n d r m mt) (J : Finset (Fin mt))
    (z : Fin d ⊕ Fin r → ℝ) :
    (∀ k, (liftMat M J *ᵥ z) (Sum.inl k) = (M.G *ᵥ fun i => z (Sum.inl i)) k) ∧
    (∀ j, (liftMat M J *ᵥ z) (Sum.inr (Sum.inl j)) =
      (M.W *ᵥ fun l => z (Sum.inr l)) j - (M.H *ᵥ fun i => z (Sum.inl i)) j) ∧
    (∀ k, (liftMat M J *ᵥ z) (Sum.inr (Sum.inr k)) =
      if k ∈ J then -(M.G *ᵥ fun i => z (Sum.inl i)) k else 0) := by
  refine ⟨fun k => ?_, fun j => ?_, fun k => ?_⟩
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, liftMat]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, liftMat, Finset.sum_neg_distrib]
    ring
  · by_cases hk : k ∈ J
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, liftMat, hk, Finset.sum_neg_distrib]
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, liftMat, hk]

/-- `|(Gv)_k| ≤ K ‖v‖`. -/
theorem G_bound (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : Fin d → ℝ) (k : Fin mt) :
    |(M.G *ᵥ v) k| ≤ (1 + ∑ k, ∑ i, |M.G k i|) * ‖WithLp.toLp p v‖ := by
  have hv : ∀ i, |v i| ≤ ‖WithLp.toLp p v‖ := fun i => by
    have := PiLp.norm_apply_le (WithLp.toLp p v) i
    simpa [Real.norm_eq_abs] using this
  calc |(M.G *ᵥ v) k| = |∑ i, M.G k i * v i| := rfl
    _ ≤ ∑ i, |M.G k i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |M.G k i| * |v i| := by simp [abs_mul]
    _ ≤ ∑ i, |M.G k i| * ‖WithLp.toLp p v‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = (∑ i, |M.G k i|) * ‖WithLp.toLp p v‖ := by rw [Finset.sum_mul]
    _ ≤ (1 + ∑ k, ∑ i, |M.G k i|) * ‖WithLp.toLp p v‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have := Finset.single_le_sum (f := fun k => ∑ i, |M.G k i|)
          (fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ k)
        linarith

/-- `‖v‖ ≤ K_d max_i |v_i|`. -/
theorem norm_le_of_coord (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : Fin d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) :
    ‖WithLp.toLp p v‖ ≤
      (1 + ∑ i, ‖WithLp.toLp p (fun j : Fin d => if i = j then (1 : ℝ) else 0)‖) * B := by
  classical
  set e : Fin d → (Fin d → ℝ) := fun i j => if i = j then (1 : ℝ) else 0
  have hdecomp : WithLp.toLp p v = ∑ i, v i • WithLp.toLp p (e i) := by
    conv_lhs => rw [pi_eq_sum_univ v]
    rw [WithLp.toLp_sum]
    simp [WithLp.toLp_smul, e]
  rw [hdecomp]
  calc ‖∑ i, v i • WithLp.toLp p (e i)‖ ≤ ∑ i, ‖v i • WithLp.toLp p (e i)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| * ‖WithLp.toLp p (e i)‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, B * ‖WithLp.toLp p (e i)‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
    _ = B * ∑ i, ‖WithLp.toLp p (e i)‖ := by rw [Finset.mul_sum]
    _ ≤ B * (1 + ∑ i, ‖WithLp.toLp p (e i)‖) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hB
    _ = (1 + ∑ i, ‖WithLp.toLp p (e i)‖) * B := by ring

/-- Pigeonhole: among `mt + 1` consecutive intervals, one contains no slack value. -/
theorem pigeonhole (s : Fin mt → ℝ) (τ : ℕ → ℝ) (hτ : Monotone τ) :
    ∃ ℓ : ℕ, ℓ ≤ mt ∧ ∀ k, ¬ (τ ℓ ≤ s k ∧ s k < τ (ℓ + 1)) := by
  by_contra h
  push Not at h
  have h' : ∀ ℓ : Fin (mt + 1), ∃ k, τ ℓ ≤ s k ∧ s k < τ (ℓ + 1) :=
    fun ℓ => h ℓ (Nat.lt_succ_iff.1 ℓ.2)
  choose f hf using h'
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hlt | hlt
    · have h1 := (hf a).2
      have h2 := (hf b).1
      rw [hab] at h1
      have : τ ((a : ℕ) + 1) ≤ τ b := hτ (by omega)
      linarith
    · have h1 := (hf b).2
      have h2 := (hf a).1
      rw [← hab] at h1
      have : τ ((b : ℕ) + 1) ≤ τ a := hτ (by omega)
      linarith
  have := Fintype.card_le_of_injective f hinj
  simp at this

end SROEq3Aux

open TwoStageSRO.AsymOpt SROLP SROEq3Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (εbar : ℝ) (hεbar : 0 < εbar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ zhat ∈ XiStar M xs, ∃ zbar ∈ XiStar M xs,
      ball p zhat ε ∩ Xi M ⊆
        (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by
  classical
  obtain ⟨hlam0, hlam1⟩ := hlam
  -- Hoffman constants and infeasibility gaps for every index set `J`
  have hJ : ∀ J : Finset (Fin mt), ∃ θJ cJ : ℝ, 0 ≤ θJ ∧ 0 < cJ ∧
      ((∃ z, liftRhs M xs J ≤ liftMat M J *ᵥ z) →
        ∀ z0 : Fin d ⊕ Fin r → ℝ, ∀ ρ : ℝ, 0 ≤ ρ →
          (∀ i, liftRhs M xs J i - (liftMat M J *ᵥ z0) i ≤ ρ) →
          ∃ z, liftRhs M xs J ≤ liftMat M J *ᵥ z ∧ ∀ k, |z k - z0 k| ≤ θJ * ρ) ∧
      ((¬ ∃ z, liftRhs M xs J ≤ liftMat M J *ᵥ z) →
        ∀ z0 : Fin d ⊕ Fin r → ℝ, ∃ i, cJ ≤ liftRhs M xs J i - (liftMat M J *ᵥ z0) i) := by
    intro J
    by_cases hfe : ∃ z, liftRhs M xs J ≤ liftMat M J *ᵥ z
    · obtain ⟨θJ, hθJ, hH⟩ := hoffman (liftMat M J) (liftRhs M xs J) hfe
      exact ⟨θJ, 1, hθJ, one_pos, fun _ => hH, fun h => absurd hfe h⟩
    · obtain ⟨cJ, hcJ, hG⟩ := infeasible_gap (liftMat M J) (liftRhs M xs J) hfe
      exact ⟨0, cJ, le_rfl, hcJ, fun h => absurd h hfe, fun _ => hG⟩
  choose θJ cJ hθJ hcJ hHoff hGap using hJ
  set θ : ℝ := ∑ J : Finset (Fin mt), θJ J with hθ
  have hθ0 : 0 ≤ θ := Finset.sum_nonneg fun J _ => hθJ J
  have hθle : ∀ J, θJ J ≤ θ := fun J =>
    Finset.single_le_sum (fun J _ => hθJ J) (Finset.mem_univ J)
  set c : ℝ := Finset.univ.inf' ⟨∅, Finset.mem_univ _⟩ cJ with hc
  have hcpos : 0 < c := (Finset.lt_inf'_iff _).2 fun J _ => hcJ J
  have hcle : ∀ J, c ≤ cJ J := fun J => Finset.inf'_le _ (Finset.mem_univ J)
  set K : ℝ := 1 + ∑ k, ∑ i, |M.G k i| with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ k, ∑ i, |M.G k i| :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set Kd : ℝ := 1 + ∑ i, ‖WithLp.toLp p (fun j : Fin d => if i = j then (1 : ℝ) else 0)‖
    with hKd
  have hKd1 : 1 ≤ Kd := by
    have : 0 ≤ ∑ i, ‖WithLp.toLp p (fun j : Fin d => if i = j then (1 : ℝ) else 0)‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (K + K * Kd * θ) / lam + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (K + K * Kd * θ) / lam := div_nonneg (by positivity) hlam0.le
    linarith
  have hlamA : K + K * Kd * θ ≤ lam * A := by
    rw [hA, mul_add lam, mul_div_cancel₀ _ hlam0.ne']
    linarith
  set P : ℝ := A ^ mt with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hA1
  set ε : ℝ := min (c / (P + 1)) (lam * εbar / (1 + Kd * θ * P)) with hε
  have hεpos : 0 < ε := lt_min (div_pos hcpos (by linarith)) (div_pos (mul_pos hlam0 hεbar)
    (by positivity))
  have hεc : ε * P < c := by
    have h1 : ε ≤ c / (P + 1) := min_le_left _ _
    have h2 : ε * (P + 1) ≤ c := by rwa [le_div_iff₀ (by linarith)] at h1
    have e : ε * P = ε * (P + 1) - ε := by ring
    linarith
  have hεball : ε + Kd * θ * (ε * P) ≤ lam * εbar := by
    have h1 : ε ≤ lam * εbar / (1 + Kd * θ * P) := min_le_right _ _
    have h2 : ε * (1 + Kd * θ * P) ≤ lam * εbar := by
      rwa [le_div_iff₀ (by positivity)] at h1
    have e : ε + Kd * θ * (ε * P) = ε * (1 + Kd * θ * P) := by ring
    linarith
  refine ⟨ε, hεpos, fun zhat hzhat => ?_⟩
  obtain ⟨hzX, yhat, hyhat⟩ := hzhat
  -- slacks and thresholds
  set s : Fin mt → ℝ := fun k => (M.G *ᵥ zhat) k - M.g0 k with hs
  have hs0 : ∀ k, 0 ≤ s k := fun k => by simp only [hs]; linarith [hzX k]
  set τ : ℕ → ℝ := fun ℓ => ε * A ^ ℓ with hτ
  have hτmono : Monotone τ := fun a b hab =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 hab) hεpos.le
  obtain ⟨ℓ, hℓ, hgap⟩ := pigeonhole s τ hτmono
  have hτℓε : ε ≤ τ ℓ := le_mul_of_one_le_right hεpos.le (one_le_pow₀ hA1)
  have hτℓP : τ ℓ ≤ ε * P := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 hℓ) hεpos.le
  have hτsucc : τ (ℓ + 1) = A * τ ℓ := by simp only [hτ, pow_succ]; ring
  set J := Finset.univ.filter (fun k => s k < τ ℓ) with hJdef
  set z0 : Fin d ⊕ Fin r → ℝ := Sum.elim zhat yhat with hz0
  have hev0 := liftMat_mulVec M J z0
  have hz0ζ : (fun i => z0 (Sum.inl i)) = zhat := rfl
  have hz0y : (fun l => z0 (Sum.inr l)) = yhat := rfl
  -- violations of `z0`
  have hviol : ∀ i, liftRhs M xs J i - (liftMat M J *ᵥ z0) i ≤ τ ℓ := by
    rintro (k | j | k)
    · rw [hev0.1 k, hz0ζ]
      simp only [liftRhs]
      linarith [hzX k, hτℓε]
    · rw [hev0.2.1 j, hz0ζ, hz0y]
      simp only [liftRhs]
      have := hyhat j
      simp only [Model.h, Pi.add_apply] at this
      linarith [hτℓε]
    · rw [hev0.2.2 k, hz0ζ]
      simp only [liftRhs]
      by_cases hk : k ∈ J
      · simp only [hk, if_true]
        have : s k < τ ℓ := by simpa [hJdef] using hk
        simp only [hs] at this
        linarith
      · simp only [hk, if_false, sub_zero]
        linarith [hτℓε]
  -- the face `J` is feasible, by the gap estimate
  have hfe : ∃ z, liftRhs M xs J ≤ liftMat M J *ᵥ z := by
    by_contra hfe
    obtain ⟨i, hi⟩ := hGap J hfe z0
    have h1 := hviol i
    have h2 := hcle J
    linarith
  obtain ⟨z, hz, hzdist⟩ := hHoff J hfe z0 (τ ℓ) (by linarith) hviol
  have hevz := liftMat_mulVec M J z
  set zbar : Fin d → ℝ := fun i => z (Sum.inl i) with hzbar
  set ybar : Fin r → ℝ := fun l => z (Sum.inr l) with hybar
  have hzbarX : zbar ∈ Xi M := fun k => by
    have := hz (Sum.inl k); rw [hevz.1 k] at this; exact this
  have hzbarStar : zbar ∈ XiStar M xs := by
    refine ⟨hzbarX, ybar, fun j => ?_⟩
    have := hz (Sum.inr (Sum.inl j))
    rw [hevz.2.1 j] at this
    simp only [liftRhs] at this
    simp only [Model.h, Pi.add_apply]
    linarith
  have hzbarJ : ∀ k ∈ J, (M.G *ᵥ zbar) k = M.g0 k := by
    intro k hk
    have h1 := hz (Sum.inr (Sum.inr k))
    rw [hevz.2.2 k] at h1
    simp only [liftRhs, hk, if_true] at h1
    exact le_antisymm (by linarith) (hzbarX k)
  -- distance from `zhat` to `zbar`
  have hdist : ‖WithLp.toLp p (zbar - zhat)‖ ≤ Kd * (θ * τ ℓ) := by
    have hBnn : 0 ≤ θ * τ ℓ := mul_nonneg hθ0 (by linarith)
    refine norm_le_of_coord p _ _ hBnn fun i => ?_
    have := hzdist (Sum.inl i)
    calc |(zbar - zhat) i| = |z (Sum.inl i) - z0 (Sum.inl i)| := rfl
      _ ≤ θJ J * τ ℓ := this
      _ ≤ θ * τ ℓ := mul_le_mul_of_nonneg_right (hθle J) (by linarith)
  refine ⟨zbar, hzbarStar, ?_⟩
  rintro ζ ⟨hζb, hζX⟩
  have hζb' : ‖WithLp.toLp p (ζ - zhat)‖ ≤ ε := hζb
  refine ⟨zbar + lam⁻¹ • (ζ - zbar), ⟨?_, ?_⟩, ?_⟩
  · -- in the ball of radius `ε̄`
    show ‖WithLp.toLp p (zbar + lam⁻¹ • (ζ - zbar) - zbar)‖ ≤ εbar
    rw [add_sub_cancel_left, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hlam0)]
    have htri : ‖WithLp.toLp p (ζ - zbar)‖ ≤ ε + Kd * (θ * τ ℓ) := by
      have e : WithLp.toLp p (ζ - zbar) = WithLp.toLp p (ζ - zhat) - WithLp.toLp p (zbar - zhat) := by
        rw [← WithLp.toLp_sub]; congr 1; abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add hζb' hdist)
    have h2 : Kd * (θ * τ ℓ) ≤ Kd * θ * (ε * P) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hτℓP (by positivity)
    rw [inv_mul_le_iff₀ hlam0]
    linarith
  · -- in `Ξ`
    intro k
    have hlin : (M.G *ᵥ (zbar + lam⁻¹ • (ζ - zbar))) k =
        (M.G *ᵥ zbar) k + lam⁻¹ * ((M.G *ᵥ ζ) k - (M.G *ᵥ zbar) k) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]; rfl
    rw [hlin]
    -- it suffices that `s_k(ζ) ≥ (1 - λ) s_k(zbar)`
    suffices hsuff : (1 - lam) * ((M.G *ᵥ zbar) k - M.g0 k) ≤ (M.G *ᵥ ζ) k - M.g0 k by
      have : lam⁻¹ * ((M.G *ᵥ ζ) k - (M.G *ᵥ zbar) k) ≥
          lam⁻¹ * (-(lam * ((M.G *ᵥ zbar) k - M.g0 k))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hlam0.le)
        linarith
      rw [mul_neg, ← mul_assoc, inv_mul_cancel₀ hlam0.ne', one_mul] at this
      linarith
    by_cases hk : k ∈ J
    · rw [hzbarJ k hk, sub_self, mul_zero]
      linarith [hζX k]
    · have hsk : τ ℓ ≤ s k := by
        have : ¬ s k < τ ℓ := by simpa [hJdef] using hk
        linarith
      have hsk2 : A * τ ℓ ≤ s k := by
        have := hgap k
        rw [← hτsucc]
        by_contra hc
        push Not at hc
        exact this ⟨hsk, hc⟩
      have hζk : |(M.G *ᵥ (ζ - zhat)) k| ≤ K * ε :=
        (G_bound M p (ζ - zhat) k).trans (mul_le_mul_of_nonneg_left hζb' (by linarith))
      have hzk : |(M.G *ᵥ (zbar - zhat)) k| ≤ K * (Kd * (θ * τ ℓ)) :=
        (G_bound M p (zbar - zhat) k).trans (mul_le_mul_of_nonneg_left hdist (by linarith))
      rw [Matrix.mulVec_sub] at hζk hzk
      simp only [Pi.sub_apply] at hζk hzk
      have hζk' := neg_abs_le ((M.G *ᵥ ζ) k - (M.G *ᵥ zhat) k)
      have hzk' := le_abs_self ((M.G *ᵥ zbar) k - (M.G *ᵥ zhat) k)
      have hskdef : s k = (M.G *ᵥ zhat) k - M.g0 k := rfl
      -- `λ s_k ≥ K ε + K K_d θ τ_ℓ`
      have hkey : K * ε + K * (Kd * (θ * τ ℓ)) ≤ lam * s k := by
        have h1 : (K + K * Kd * θ) * τ ℓ ≤ lam * A * τ ℓ :=
          mul_le_mul_of_nonneg_right hlamA (by linarith)
        have h2 : lam * A * τ ℓ ≤ lam * s k := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsk2 hlam0.le
        have h3 : K * ε ≤ K * τ ℓ := mul_le_mul_of_nonneg_left hτℓε (by linarith)
        have e : (K + K * Kd * θ) * τ ℓ = K * τ ℓ + K * (Kd * (θ * τ ℓ)) := by ring
        linarith
      have hpos : 0 ≤ K * (Kd * (θ * τ ℓ)) := by
        have : 0 ≤ τ ℓ := by linarith
        positivity
      set Bz := K * (Kd * (θ * τ ℓ)) with hBz
      have hb1 : (M.G *ᵥ zbar) k - M.g0 k ≤ s k + Bz := by
        rw [hskdef]
        have := abs_le.1 hzk
        linarith
      have hm1 : (1 - lam) * ((M.G *ᵥ zbar) k - M.g0 k) ≤ (1 - lam) * (s k + Bz) :=
        mul_le_mul_of_nonneg_left hb1 (by linarith)
      have hm2 : (1 - lam) * (s k + Bz) = s k + Bz - lam * s k - lam * Bz := by ring
      have hm3 : 0 ≤ lam * Bz := mul_nonneg hlam0.le hpos
      have hζlow : -(K * ε) ≤ (M.G *ᵥ ζ) k - (M.G *ᵥ zhat) k := by
        have := abs_le.1 hζk
        linarith
      rw [hskdef] at hkey hm2 hm1
      linarith
  · show lam • (zbar + lam⁻¹ • (ζ - zbar)) + (1 - lam) • zbar = ζ
    rw [smul_add, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
