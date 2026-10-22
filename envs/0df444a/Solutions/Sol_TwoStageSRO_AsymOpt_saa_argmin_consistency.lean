-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.saa_argmin_consistency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:51:51.5378+00:00
-- url     : https://prove2.me/submissions/97645a30-aa67-4d57-bb59-117555d655aa

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

namespace SROSAAAux
open TwoStageSRO.AsymOpt SROLP SROMeasAux

variable {n d r m mt : ℕ}

/-- `x` admits a feasible recourse at `ζ`. -/
def feas (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) : Prop :=
  ∃ y : Fin r → ℝ, M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y

theorem Q_top_of_not_feas (M : Model n d r m mt) {x : Fin n → ℝ} {ζ : Fin d → ℝ}
    (h : ¬ feas M x ζ) : Q M x ζ = ⊤ := by
  unfold Q
  rw [sInf_eq_top]
  rintro _ ⟨y, hy, rfl⟩
  exact absurd ⟨y, hy⟩ h

theorem Q_lt_top_iff (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) :
    Q M x ζ < ⊤ → feas M x ζ := by
  intro hQ
  by_contra h
  rw [Q_top_of_not_feas M h] at hQ
  exact lt_irrefl _ hQ

/-- The finite set of vertices of the dual polyhedron `D`. -/
noncomputable def extD (M : Model n d r m mt) : Finset (Fin m → ℝ) :=
  (extremePoints_finite M.W M.q).toFinset

theorem mem_extD (M : Model n d r m mt) {δ : Fin m → ℝ} :
    δ ∈ extD M ↔ δ ∈ Set.extremePoints ℝ (stdPoly M.W M.q) := by
  simp [extD]

theorem extD_nonempty (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty) :
    (extD M).Nonempty := by
  obtain ⟨δ0, hδ0⟩ := hD
  obtain ⟨δ, hδ, -⟩ := exists_extreme_ge M.W M.q 0 0 (fun δ _ => by simp) _ δ0 hδ0 rfl
  exact ⟨δ, (mem_extD M).2 hδ⟩

/-- The piecewise-linear dual representation `φ(x, ζ) = max_{δ ∈ ext D} δᵀ(h(ζ) - Tx)`. -/
noncomputable def phi (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) : ℝ :=
  if h : (extD M).Nonempty then (extD M).sup' h (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)) else 0

theorem phi_eq (M : Model n d r m mt) (h : (extD M).Nonempty) (x : Fin n → ℝ) (ζ : Fin d → ℝ) :
    phi M x ζ = (extD M).sup' h (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)) := dif_pos h

/-- Strong duality for the recourse problem. -/
theorem Q_eq_phi (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty) {x : Fin n → ℝ}
    {ζ : Fin d → ℝ} (hf : feas M x ζ) : Q M x ζ = ((phi M x ζ : ℝ) : EReal) := by
  have hE := extD_nonempty M hD
  obtain ⟨y1, hy1⟩ := hf
  have hb1 : M.h ζ - M.T *ᵥ x ≤ M.W *ᵥ y1 := by
    intro j; have := hy1 j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
  apply le_antisymm
  · obtain ⟨δ, hδ, y, hy, hqy⟩ := lp_vertex M.W (M.h ζ - M.T *ᵥ x) M.q ⟨y1, hb1⟩ hD
    have hyf : M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y := by
      intro j; have := hy j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    unfold Q
    refine (sInf_le (show ((M.q ⬝ᵥ y : ℝ) : EReal) ∈ {v : EReal | ∃ y : Fin r → ℝ,
      M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y ∧ v = ((M.q ⬝ᵥ y : ℝ) : EReal)} from ⟨y, hyf, rfl⟩)).trans
      (EReal.coe_le_coe_iff.2 ?_)
    rw [phi_eq M hE]
    exact hqy.trans (Finset.le_sup' (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)) ((mem_extD M).2 hδ))
  · unfold Q
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    refine EReal.coe_le_coe_iff.2 ?_
    rw [phi_eq M hE]
    refine Finset.sup'_le _ _ fun δ hδ => ?_
    refine weak_duality M.W _ M.q ((mem_extD M).1 hδ).1 ?_
    intro j; have := hy j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith

theorem phi_le_Q (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty) (x : Fin n → ℝ)
    (ζ : Fin d → ℝ) : ((phi M x ζ : ℝ) : EReal) ≤ Q M x ζ := by
  by_cases hf : feas M x ζ
  · rw [Q_eq_phi M hD hf]
  · rw [Q_top_of_not_feas M hf]; exact le_top

theorem Q_ne_bot (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty) (x : Fin n → ℝ)
    (ζ : Fin d → ℝ) : Q M x ζ ≠ ⊥ := by
  intro h
  have := phi_le_Q M hD x ζ
  rw [h] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.1 this)

/-- A Lipschitz constant (in the sup norm) of `x ↦ φ(x, ζ)`, uniform in `ζ`. -/
noncomputable def LT (M : Model n d r m mt) : ℝ := ∑ δ ∈ extD M, ∑ k, |(M.Tᵀ *ᵥ δ) k|

theorem LT_nonneg (M : Model n d r m mt) : 0 ≤ LT M :=
  Finset.sum_nonneg fun δ _ => Finset.sum_nonneg fun k _ => abs_nonneg _

theorem dot_le_norm {k : ℕ} (a v : Fin k → ℝ) : |a ⬝ᵥ v| ≤ (∑ i, |a i|) * ‖v‖ := by
  calc |a ⬝ᵥ v| = |∑ i, a i * v i| := rfl
    _ ≤ ∑ i, |a i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |v i| := by simp [abs_mul]
    _ ≤ ∑ i, |a i| * ‖v‖ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i)
          (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖v‖ := by rw [Finset.sum_mul]

theorem phi_lip (M : Model n d r m mt) (x1 x2 : Fin n → ℝ) (ζ : Fin d → ℝ) :
    phi M x1 ζ ≤ phi M x2 ζ + LT M * ‖x1 - x2‖ := by
  by_cases hE : (extD M).Nonempty
  · rw [phi_eq M hE, phi_eq M hE]
    refine Finset.sup'_le _ _ fun δ hδ => ?_
    have h1 : δ ⬝ᵥ (M.h ζ - M.T *ᵥ x1) = δ ⬝ᵥ (M.h ζ - M.T *ᵥ x2) -
        (M.Tᵀ *ᵥ δ) ⬝ᵥ (x1 - x2) := by
      rw [mulVec_transpose, ← dotProduct_mulVec, Matrix.mulVec_sub, dotProduct_sub,
        dotProduct_sub, dotProduct_sub]
      ring
    have h2 : -((M.Tᵀ *ᵥ δ) ⬝ᵥ (x1 - x2)) ≤ (∑ k, |(M.Tᵀ *ᵥ δ) k|) * ‖x1 - x2‖ :=
      (neg_le_abs _).trans (dot_le_norm _ _)
    have h3 : (∑ k, |(M.Tᵀ *ᵥ δ) k|) ≤ LT M :=
      Finset.single_le_sum (f := fun δ => ∑ k, |(M.Tᵀ *ᵥ δ) k|)
        (fun δ _ => Finset.sum_nonneg fun k _ => abs_nonneg _) hδ
    have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (x1 - x2))
    have h5 := Finset.le_sup' (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x2)) hδ
    linarith
  · rw [phi, phi, dif_neg hE, dif_neg hE]
    have := mul_nonneg (LT_nonneg M) (norm_nonneg (x1 - x2))
    linarith

theorem phi_convex (M : Model n d r m mt) (x1 x2 : Fin n → ℝ) (ζ : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phi M ((1 - t) • x1 + t • x2) ζ ≤ (1 - t) * phi M x1 ζ + t * phi M x2 ζ := by
  by_cases hE : (extD M).Nonempty
  · rw [phi_eq M hE, phi_eq M hE, phi_eq M hE]
    refine Finset.sup'_le _ _ fun δ hδ => ?_
    have e : δ ⬝ᵥ (M.h ζ - M.T *ᵥ ((1 - t) • x1 + t • x2)) =
        (1 - t) * (δ ⬝ᵥ (M.h ζ - M.T *ᵥ x1)) + t * (δ ⬝ᵥ (M.h ζ - M.T *ᵥ x2)) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_sub, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [e]
    have h1 := Finset.le_sup' (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x1)) hδ
    have h2 := Finset.le_sup' (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x2)) hδ
    have := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 - t)
    have := mul_le_mul_of_nonneg_left h2 ht0
    linarith
  · simp [phi, hE]

theorem phi_measurable (M : Model n d r m mt) (x : Fin n → ℝ) : Measurable (phi M x) := by
  by_cases hE : (extD M).Nonempty
  · have : phi M x = (extD M).sup' hE (fun δ ζ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)) := by
      funext ζ; rw [phi_eq M hE, Finset.sup'_apply]
    rw [this]
    refine Finset.measurable_sup' hE fun δ _ => ?_
    refine Continuous.measurable ?_
    unfold Model.h
    exact continuous_const.dotProduct ((continuous_const.add
      (continuous_const.matrix_mulVec continuous_id)).sub continuous_const)
  · have : phi M x = fun _ => (0 : ℝ) := funext fun ζ => dif_neg hE
    rw [this]; exact measurable_const

/-- A linear growth bound for `φ` in `ζ`. -/
theorem phi_abs_le (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) :
    |phi M x ζ| ≤ ∑ δ ∈ extD M, (|δ ⬝ᵥ (M.h0 - M.T *ᵥ x)| +
      (∑ j, |δ j| * ∑ i, |M.H j i|) * ‖ζ‖) := by
  have hterm : ∀ δ : Fin m → ℝ, |δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)| ≤
      |δ ⬝ᵥ (M.h0 - M.T *ᵥ x)| + (∑ j, |δ j| * ∑ i, |M.H j i|) * ‖ζ‖ := by
    intro δ
    have e : δ ⬝ᵥ (M.h ζ - M.T *ᵥ x) = δ ⬝ᵥ (M.h0 - M.T *ᵥ x) + δ ⬝ᵥ (M.H *ᵥ ζ) := by
      simp only [Model.h, dotProduct_sub, dotProduct_add]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    calc |δ ⬝ᵥ (M.H *ᵥ ζ)| = |∑ j, δ j * (M.H *ᵥ ζ) j| := rfl
      _ ≤ ∑ j, |δ j * (M.H *ᵥ ζ) j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |δ j| * |(M.H *ᵥ ζ) j| := by simp [abs_mul]
      _ ≤ ∑ j, |δ j| * ((∑ i, |M.H j i|) * ‖ζ‖) := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (dot_le_norm (M.H j) ζ) (abs_nonneg _)
      _ = (∑ j, |δ j| * ∑ i, |M.H j i|) * ‖ζ‖ := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
  have hnn : ∀ δ ∈ extD M, 0 ≤ |δ ⬝ᵥ (M.h0 - M.T *ᵥ x)| +
      (∑ j, |δ j| * ∑ i, |M.H j i|) * ‖ζ‖ := fun δ _ => by positivity
  by_cases hE : (extD M).Nonempty
  · rw [phi_eq M hE, abs_le]
    obtain ⟨δ0, hδ0⟩ := hE
    constructor
    · have h1 := Finset.le_sup' (fun δ => δ ⬝ᵥ (M.h ζ - M.T *ᵥ x)) hδ0
      have h2 := neg_abs_le (δ0 ⬝ᵥ (M.h ζ - M.T *ᵥ x))
      have h3 := hterm δ0
      have h4 := Finset.single_le_sum hnn hδ0
      linarith
    · refine Finset.sup'_le _ _ fun δ hδ => ?_
      have h2 := le_abs_self (δ ⬝ᵥ (M.h ζ - M.T *ᵥ x))
      have h3 := hterm δ
      have h4 := Finset.single_le_sum hnn hδ
      linarith
  · rw [phi, dif_neg hE, abs_zero]
    exact Finset.sum_nonneg hnn

theorem phi_integrable (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (x : Fin n → ℝ) : Integrable (phi M x) μ := by
  refine Integrable.mono' (g := fun ζ => ∑ δ ∈ extD M, (|δ ⬝ᵥ (M.h0 - M.T *ᵥ x)| +
      (∑ j, |δ j| * ∑ i, |M.H j i|) * ‖ζ‖)) ?_ (phi_measurable M x).aestronglyMeasurable ?_
  · refine integrable_finsetSum _ fun δ _ => ?_
    exact (integrable_const _).add (hint.norm.const_mul _)
  · exact Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs]; exact phi_abs_le M x ζ

/-- The normalized cone of Farkas certificates `{λ ≥ 0 : Wᵀλ = 0, Σλ = 1}` as a standard-form
polyhedron. -/
noncomputable def Wc (M : Model n d r m mt) : Matrix (Fin m) (Option (Fin r)) ℝ :=
  fun j o => match o with
  | none => 1
  | some l => M.W j l

def qc : Option (Fin r) → ℝ := fun o => match o with
  | none => 1
  | some _ => 0

theorem mem_Pc (M : Model n d r m mt) (l : Fin m → ℝ) :
    l ∈ stdPoly (Wc M) qc ↔ (∑ j, l j = 1 ∧ M.Wᵀ *ᵥ l = 0) ∧ 0 ≤ l := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, h2⟩
    · have := congrFun h1 none
      simpa [Wc, qc, mulVec, dotProduct, transpose_apply] using this
    · funext l'
      have := congrFun h1 (some l')
      simpa [Wc, qc, mulVec, dotProduct, transpose_apply] using this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨funext fun o => ?_, h3⟩
    cases o with
    | none => simpa [Wc, qc, mulVec, dotProduct, transpose_apply] using h1
    | some l' =>
      have := congrFun h2 l'
      simpa [Wc, qc, mulVec, dotProduct, transpose_apply] using this

/-- The vertices of the normalized certificate polyhedron. -/
noncomputable def extR (M : Model n d r m mt) : Finset (Fin m → ℝ) :=
  (extremePoints_finite (Wc M) qc).toFinset

/-- Feasibility of the recourse problem is cut out by finitely many linear inequalities. -/
theorem feas_iff (M : Model n d r m mt) (x : Fin n → ℝ) (ζ : Fin d → ℝ) :
    feas M x ζ ↔ ∀ l ∈ extR M, l ⬝ᵥ (M.h ζ - M.T *ᵥ x) ≤ 0 := by
  constructor
  · rintro ⟨y, hy⟩ l hl
    have hlP : l ∈ stdPoly (Wc M) qc := by
      have := (Set.Finite.mem_toFinset _).1 hl
      exact this.1
    obtain ⟨⟨-, hWl⟩, hl0⟩ := (mem_Pc M l).1 hlP
    have hb : M.h ζ - M.T *ᵥ x ≤ M.W *ᵥ y := by
      intro j; have := hy j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    have := weak_duality M.W _ 0 ⟨hWl, hl0⟩ hb
    simpa using this
  · intro hall
    by_contra hnf
    have hno : ¬ ∃ y, M.h ζ - M.T *ᵥ x ≤ M.W *ᵥ y := by
      rintro ⟨y, hy⟩
      apply hnf
      refine ⟨y, fun j => ?_⟩
      have := hy j; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    obtain ⟨l, hl, hWl, hlb⟩ := farkas_ineq M.W _ hno
    set b := M.h ζ - M.T *ᵥ x with hb
    set S := ∑ j, l j with hS
    have hSpos : 0 < S := by
      rcases (Finset.sum_nonneg fun j _ => hl j : 0 ≤ S).lt_or_eq with h | h
      · exact h
      · exfalso
        have hl0 : ∀ j, l j = 0 := fun j =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hl j)).1 h.symm j (Finset.mem_univ j)
        have : l ⬝ᵥ b = 0 := by simp [dotProduct, hl0]
        linarith
    have hl1 : S⁻¹ • l ∈ stdPoly (Wc M) qc := by
      refine (mem_Pc M _).2 ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hS]
        exact inv_mul_cancel₀ hSpos.ne'
      · rw [mulVec_smul, hWl, smul_zero]
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg (inv_nonneg.2 hSpos.le) (hl j)
    have hbdd : ∀ lw ∈ stdPoly (Wc M) qc, lw ⬝ᵥ b ≤ ∑ j, |b j| := by
      intro lw hlw
      obtain ⟨⟨h1, -⟩, h0⟩ := (mem_Pc M lw).1 hlw
      refine Finset.sum_le_sum fun j _ => ?_
      have hle1 : lw j ≤ 1 := by
        rw [← h1]
        exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j)
      calc lw j * b j ≤ lw j * |b j| := mul_le_mul_of_nonneg_left (le_abs_self _) (h0 j)
        _ ≤ 1 * |b j| := mul_le_mul_of_nonneg_right hle1 (abs_nonneg _)
        _ = |b j| := one_mul _
    obtain ⟨l', hl', hle⟩ := exists_extreme_ge (Wc M) qc b _ hbdd _ _ hl1 rfl
    have hpos : 0 < (S⁻¹ • l) ⬝ᵥ b := by
      rw [smul_dotProduct, smul_eq_mul]
      exact mul_pos (inv_pos.2 hSpos) hlb
    have := hall l' ((Set.Finite.mem_toFinset _).2 hl')
    linarith

end SROSAAAux

namespace SROSAAAux
open TwoStageSRO.AsymOpt SROLP SROMeasAux

variable {n d r m mt : ℕ}

theorem isClosed_feas (M : Model n d r m mt) (x : Fin n → ℝ) : IsClosed {ζ | feas M x ζ} := by
  have : {ζ | feas M x ζ} = ⋂ l ∈ extR M, {ζ | l ⬝ᵥ (M.h ζ - M.T *ᵥ x) ≤ 0} := by
    ext ζ; simp [feas_iff]
  rw [this]
  refine isClosed_biInter fun l _ => isClosed_le ?_ continuous_const
  unfold Model.h
  exact continuous_const.dotProduct ((continuous_const.add
    (continuous_const.matrix_mulVec continuous_id)).sub continuous_const)

theorem lintegral_ofReal_ne_top {μ : Measure (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f μ) : ∫⁻ ζ, ENNReal.ofReal (f ζ) ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top hf.2.ne (lintegral_mono fun ζ => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- `V*(x) = cᵀx + ∫ φ(x, ·) dμ` when `x` has a feasible recourse `μ`-a.e. -/
theorem Vstar_of_feas (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (x : Fin n → ℝ) (hF : μ {ζ | ¬ feas M x ζ} = 0) :
    Vstar M μ x = ((M.c ⬝ᵥ x + ∫ ζ, phi M x ζ ∂μ : ℝ) : EReal) := by
  have hfi := phi_integrable M μ hint x
  have hae : ∀ᵐ ζ ∂μ, Q M x ζ = ((phi M x ζ : ℝ) : EReal) := by
    have : ∀ᵐ ζ ∂μ, feas M x ζ := by rw [ae_iff]; exact hF
    filter_upwards [this] with ζ hζ using Q_eq_phi M hD hζ
  have hA : ∫⁻ ζ, (Q M x ζ).toENNReal ∂μ = ∫⁻ ζ, ENNReal.ofReal (phi M x ζ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ζ hζ
    rw [hζ, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have hB : ∫⁻ ζ, (-Q M x ζ).toENNReal ∂μ = ∫⁻ ζ, ENNReal.ofReal (-phi M x ζ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ζ hζ
    rw [hζ, ← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have hAfin := lintegral_ofReal_ne_top hfi
  have hBfin : ∫⁻ ζ, ENNReal.ofReal (-phi M x ζ) ∂μ ≠ ⊤ := lintegral_ofReal_ne_top hfi.neg
  unfold Vstar DupacovaWets.Consistency.expect
  rw [hA, hB, if_neg hAfin, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi,
    ← EReal.coe_ennreal_toReal hAfin, ← EReal.coe_ennreal_toReal hBfin, ← EReal.coe_sub,
    ← EReal.coe_add]

/-- `V*(x) = +∞` when `x` lacks a feasible recourse on a set of positive measure. -/
theorem Vstar_of_not_feas (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) (x : Fin n → ℝ)
    (hF : μ {ζ | ¬ feas M x ζ} ≠ 0) : Vstar M μ x = ⊤ := by
  have hmeas : MeasurableSet {ζ | ¬ feas M x ζ} := (isClosed_feas M x).measurableSet.compl
  have hinf : ∫⁻ ζ, (Q M x ζ).toENNReal ∂μ = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ ζ, {ζ | ¬ feas M x ζ}.indicator (fun _ => (⊤ : ℝ≥0∞)) ζ ∂μ := by
          rw [lintegral_indicator_const hmeas, ENNReal.top_mul hF]
      _ ≤ ∫⁻ ζ, (Q M x ζ).toENNReal ∂μ := by
          refine lintegral_mono fun ζ => ?_
          by_cases hζ : feas M x ζ
          · simp [Set.indicator, hζ]
          · simp [Set.indicator, hζ, Q_top_of_not_feas M hζ]
  unfold Vstar DupacovaWets.Consistency.expect
  rw [if_pos hinf]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

/-- Strong law of large numbers for an integrable function of the samples. -/
theorem slln_fun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (ξ i ω))
      atTop (𝓝 (∫ ζ, f ζ ∂μ)) := by
  have hint : Integrable (fun ω => f (ξ 0 ω)) P := by
    have : Integrable f (P.map (ξ 0)) := by rw [(hlaw 0).map_eq]; exact hfi
    exact this.comp_aemeasurable (hlaw 0).aemeasurable
  have hind' := hind.comp (fun _ => f) (fun _ => hfm)
  have hident : ∀ i, IdentDistrib (fun ω => f (ξ i ω)) (fun ω => f (ξ 0 ω)) P P := by
    intro i
    have h : IdentDistrib (ξ i) (ξ 0) P P :=
      ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
    exact h.comp hfm
  have hslln := strong_law_ae (fun i ω => f (ξ i ω)) hint (fun i j hij => hind'.indepFun hij)
    hident
  have hE : ∫ ω, f (ξ 0 ω) ∂P = ∫ ζ, f ζ ∂μ := by
    rw [← (hlaw 0).map_eq, integral_map (hlaw 0).aemeasurable hfm.aestronglyMeasurable]
  filter_upwards [hslln] with ω hω
  rw [← hE]
  simpa [smul_eq_mul] using hω

/-- A set of positive probability is eventually hit by the samples. -/
theorem hit_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (A : Set (Fin d → ℝ)) (hA : MeasurableSet A) (hpos : 0 < μ A) :
    ∀ᵐ ω ∂P, ∃ i, ξ i ω ∈ A := by
  have h := slln_fun P μ ξ hind hlaw (A.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hA) ((integrable_const 1).indicator hA)
  rw [integral_indicator_const _ hA] at h
  have hpos' : 0 < μ.real A • (1 : ℝ) := by
    rw [smul_eq_mul, mul_one]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  filter_upwards [h] with ω hω
  obtain ⟨N, hN⟩ := (hω.eventually (lt_mem_nhds hpos')).exists
  by_contra hno
  push Not at hno
  have : ∑ i ∈ Finset.range N, A.indicator (fun _ => (1 : ℝ)) (ξ i ω) = 0 :=
    Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hno i) _
  rw [this, mul_zero] at hN
  exact lt_irrefl _ hN

end SROSAAAux

namespace SROSAAAux
open TwoStageSRO.AsymOpt SROLP SROMeasAux

variable {n d r m mt : ℕ}

theorem coe_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ)) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) :=
  map_sum (⟨⟨((↑) : ℝ → EReal), rfl⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s

/-- The SAA objective restricted to feasible points: `cᵀx + (1/N) Σ φ(x, sᵢ)`. -/
noncomputable def PhiN (M : Model n d r m mt) (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) : ℝ :=
  M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, phi M x (s i)

noncomputable def Lc (M : Model n d r m mt) : ℝ := ∑ k, |M.c k| + LT M

theorem Lc_nonneg (M : Model n d r m mt) : 0 ≤ Lc M :=
  add_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _) (LT_nonneg M)

theorem PhiN_le_VSAA (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) :
    ((PhiN M s N x : ℝ) : EReal) ≤ VSAA M s N x := by
  have hN : (0 : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg N)
  unfold PhiN VSAA
  rw [EReal.coe_add, EReal.coe_mul, coe_sum']
  gcongr with i hi
  exact phi_le_Q M hD x (s i)

theorem VSAA_eq_PhiN (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) (hf : ∀ i < N, feas M x (s i)) :
    VSAA M s N x = ((PhiN M s N x : ℝ) : EReal) := by
  unfold PhiN VSAA
  rw [EReal.coe_add, EReal.coe_mul, coe_sum']
  congr 2
  exact Finset.sum_congr rfl fun i hi => Q_eq_phi M hD (hf i (Finset.mem_range.1 hi))

theorem sum_eq_top {ι : Type*} (s : Finset ι) (f : ι → EReal) (hbot : ∀ i ∈ s, f i ≠ ⊥)
    {i0 : ι} (hi0 : i0 ∈ s) (htop : f i0 = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  rw [← Finset.add_sum_erase s f hi0, htop]
  refine EReal.top_add_of_ne_bot ?_
  refine Finset.sum_induction _ (fun a => a ≠ ⊥) (fun a b ha hb => ?_) (by simp)
    (fun i hi => hbot i (Finset.mem_of_mem_erase hi))
  exact EReal.add_ne_bot_iff.2 ⟨ha, hb⟩

theorem VSAA_top (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) {i0 : ℕ} (hi0 : i0 < N)
    (hnf : ¬ feas M x (s i0)) : VSAA M s N x = ⊤ := by
  unfold VSAA
  have hsum : ∑ i ∈ Finset.range N, Q M x (s i) = ⊤ :=
    sum_eq_top _ _ (fun i _ => Q_ne_bot M hD x (s i)) (Finset.mem_range.2 hi0)
      (Q_top_of_not_feas M hnf)
  have hNpos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (show 0 < N by omega))
  rw [hsum, EReal.coe_mul_top_of_pos hNpos]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

theorem dot_c_le (M : Model n d r m mt) (x1 x2 : Fin n → ℝ) :
    M.c ⬝ᵥ x1 ≤ M.c ⬝ᵥ x2 + (∑ k, |M.c k|) * ‖x1 - x2‖ := by
  have h := dot_le_norm M.c (x1 - x2)
  rw [dotProduct_sub] at h
  linarith [le_abs_self (M.c ⬝ᵥ x1 - M.c ⬝ᵥ x2)]

theorem PhiN_lip (M : Model n d r m mt) (s : ℕ → Fin d → ℝ) (N : ℕ) (x1 x2 : Fin n → ℝ) :
    PhiN M s N x1 ≤ PhiN M s N x2 + Lc M * ‖x1 - x2‖ := by
  unfold PhiN Lc
  have h1 := dot_c_le M x1 x2
  have h2 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, phi M x1 (s i) ≤
      (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, phi M x2 (s i) + LT M * ‖x1 - x2‖ := by
    have hsum : ∑ i ∈ Finset.range N, phi M x1 (s i) ≤
        ∑ i ∈ Finset.range N, phi M x2 (s i) + N * (LT M * ‖x1 - x2‖) := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.range N) => phi_lip M x1 x2 (s i)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      exact this
    have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg N)
    have := mul_le_mul_of_nonneg_left hsum hN0
    have hNN : (N : ℝ)⁻¹ * (N * (LT M * ‖x1 - x2‖)) ≤ LT M * ‖x1 - x2‖ := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp; exact mul_nonneg (LT_nonneg M) (norm_nonneg _)
      · rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h0.ne'), one_mul]
    rw [mul_add] at this
    linarith
  nlinarith [h1, h2]

theorem Phi_lip (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (x1 x2 : Fin n → ℝ) :
    M.c ⬝ᵥ x1 + ∫ ζ, phi M x1 ζ ∂μ ≤ M.c ⬝ᵥ x2 + ∫ ζ, phi M x2 ζ ∂μ + Lc M * ‖x1 - x2‖ := by
  have h1 := dot_c_le M x1 x2
  have h2 : ∫ ζ, phi M x1 ζ ∂μ ≤ ∫ ζ, phi M x2 ζ ∂μ + LT M * ‖x1 - x2‖ := by
    have h := integral_mono (f := phi M x1)
      (g := fun ζ => phi M x2 ζ + LT M * ‖x1 - x2‖) (phi_integrable M μ hint x1)
      ((phi_integrable M μ hint x2).add (integrable_const (LT M * ‖x1 - x2‖)))
      (fun ζ => phi_lip M x1 x2 ζ)
    have e : ∫ ζ, (phi M x2 ζ + LT M * ‖x1 - x2‖) ∂μ =
        ∫ ζ, phi M x2 ζ ∂μ + LT M * ‖x1 - x2‖ := by
      rw [integral_add (phi_integrable M μ hint x2) (integrable_const _), integral_const,
        probReal_univ, one_smul]
    linarith
  unfold Lc
  nlinarith [h1, h2]

theorem PhiN_convex (M : Model n d r m mt) (s : ℕ → Fin d → ℝ) (N : ℕ) (x1 x2 : Fin n → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PhiN M s N ((1 - t) • x1 + t • x2) ≤ (1 - t) * PhiN M s N x1 + t * PhiN M s N x2 := by
  unfold PhiN
  have hsum : ∑ i ∈ Finset.range N, phi M ((1 - t) • x1 + t • x2) (s i) ≤
      (1 - t) * ∑ i ∈ Finset.range N, phi M x1 (s i) +
        t * ∑ i ∈ Finset.range N, phi M x2 (s i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => phi_convex M x1 x2 (s i) t ht0 ht1
  have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg N)
  have := mul_le_mul_of_nonneg_left hsum hN0
  have e : M.c ⬝ᵥ ((1 - t) • x1 + t • x2) = (1 - t) * (M.c ⬝ᵥ x1) + t * (M.c ⬝ᵥ x2) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [e]
  nlinarith [this]

theorem feas_convex (M : Model n d r m mt) {x1 x2 : Fin n → ℝ} {ζ : Fin d → ℝ}
    (h1 : feas M x1 ζ) (h2 : feas M x2 ζ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    feas M ((1 - t) • x1 + t • x2) ζ := by
  obtain ⟨y1, hy1⟩ := h1
  obtain ⟨y2, hy2⟩ := h2
  refine ⟨(1 - t) • y1 + t • y2, fun j => ?_⟩
  have a1 := hy1 j
  have a2 := hy2 j
  simp only [Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul] at a1 a2 ⊢
  have := mul_le_mul_of_nonneg_left a1 (by linarith : (0 : ℝ) ≤ 1 - t)
  have := mul_le_mul_of_nonneg_left a2 ht0
  nlinarith

/-- **Local epi-lower bound**: below `V*(x)`, the SAA objectives are eventually uniformly larger
on a neighbourhood of `x`. -/
theorem epi_liminf (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (s : ℕ → Fin d → ℝ)
    (hphi : ∀ x' : Fin n → ℚ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ i ∈ Finset.range N, phi M (fun k => (x' k : ℝ)) (s i)) atTop
        (𝓝 (∫ ζ, phi M (fun k => (x' k : ℝ)) ζ ∂μ)))
    (hhit : ∀ l ∈ extR M, ∀ q : ℚ, 0 < μ {ζ | (q : ℝ) < l ⬝ᵥ M.h ζ} →
      ∃ i, (q : ℝ) < l ⬝ᵥ M.h (s i))
    (x : Fin n → ℝ) (a : EReal) (ha : a < Vstar M μ x) :
    ∃ U ∈ 𝓝 x, ∀ᶠ N in atTop, ∀ x' ∈ U, a < VSAA M s N x' := by
  by_cases hF : μ {ζ | ¬ feas M x ζ} = 0
  · rw [Vstar_of_feas M hD μ hint x hF] at ha
    set Φx := M.c ⬝ᵥ x + ∫ ζ, phi M x ζ ∂μ with hΦx
    obtain ⟨a', ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have ha2' : a' < Φx := EReal.coe_lt_coe_iff.1 ha2
    set g := Φx - a' with hg
    have hgpos : 0 < g := by linarith
    have hL := Lc_nonneg M
    set ρ := g / (4 * (Lc M + 1)) with hρ
    have hρpos : 0 < ρ := div_pos hgpos (by linarith)
    have hLρ : Lc M * ρ ≤ g / 4 := by
      rw [hρ, mul_div_assoc']
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    -- a rational point near `x`
    have hq : ∀ k, ∃ q : ℚ, x k - ρ < q ∧ (q : ℝ) < x k + ρ := fun k =>
      exists_rat_btwn (by linarith)
    choose xq hxq using hq
    set xr : Fin n → ℝ := fun k => (xq k : ℝ) with hxr
    have hxxr : ‖x - xr‖ < ρ := by
      rw [pi_norm_lt_iff hρpos]
      intro k
      simp only [Pi.sub_apply, hxr, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [(hxq k).1, (hxq k).2]
    refine ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρpos, ?_⟩
    have hev := (hphi xq).eventually (lt_mem_nhds (show
      (∫ ζ, phi M xr ζ ∂μ) - g / 4 < ∫ ζ, phi M xr ζ ∂μ by linarith))
    filter_upwards [hev] with N hN x' hx'
    have hx'r : ‖x' - xr‖ ≤ 2 * ρ := by
      have h1 : ‖x' - x‖ < ρ := by rw [← dist_eq_norm]; exact hx'
      calc ‖x' - xr‖ = ‖(x' - x) + (x - xr)‖ := by congr 1; abel
        _ ≤ ‖x' - x‖ + ‖x - xr‖ := norm_add_le _ _
        _ ≤ 2 * ρ := by linarith
    have hlip1 := PhiN_lip M s N xr x'
    have hlip2 := Phi_lip M μ hint x xr
    have hPhiNr : PhiN M s N xr = M.c ⬝ᵥ xr +
        (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, phi M xr (s i) := rfl
    have hm1 : Lc M * ‖xr - x'‖ ≤ Lc M * (2 * ρ) := by
      rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hx'r hL
    have hm2 : Lc M * ‖x - xr‖ ≤ Lc M * ρ := mul_le_mul_of_nonneg_left hxxr.le hL
    have hreal : a' < PhiN M s N x' := by
      linarith
    exact lt_of_lt_of_le ha1 ((EReal.coe_lt_coe_iff.2 hreal).le.trans
      (PhiN_le_VSAA M hD s N x'))
  · -- infeasible on a set of positive measure: some certificate is violated with positive
    -- probability, and the samples eventually exhibit it
    have hset : {ζ | ¬ feas M x ζ} =
        ⋃ l ∈ extR M, ⋃ q : ℚ, {ζ | l ⬝ᵥ (M.T *ᵥ x) < q ∧ (q : ℝ) < l ⬝ᵥ M.h ζ} := by
      ext ζ
      simp only [Set.mem_ofPred_eq, feas_iff, Set.mem_iUnion, not_forall, not_le, exists_prop]
      constructor
      · rintro ⟨l, hl, hlt⟩
        rw [dotProduct_sub] at hlt
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l ⬝ᵥ (M.T *ᵥ x) < l ⬝ᵥ M.h ζ by linarith)
        exact ⟨l, hl, q, hq1, hq2⟩
      · rintro ⟨l, hl, q, hq1, hq2⟩
        exact ⟨l, hl, by rw [dotProduct_sub]; linarith⟩
    rw [hset] at hF
    obtain ⟨l, hl, hlpos⟩ : ∃ l ∈ extR M,
        μ (⋃ q : ℚ, {ζ | l ⬝ᵥ (M.T *ᵥ x) < q ∧ (q : ℝ) < l ⬝ᵥ M.h ζ}) ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hF
      exact (measure_biUnion_null_iff (Finset.countable_toSet _)).2 hno
    obtain ⟨q, hqpos⟩ : ∃ q : ℚ, μ {ζ | l ⬝ᵥ (M.T *ᵥ x) < q ∧ (q : ℝ) < l ⬝ᵥ M.h ζ} ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hlpos (measure_iUnion_null_iff.2 hno)
    have hlq : l ⬝ᵥ (M.T *ᵥ x) < q := by
      by_contra hc
      apply hqpos
      convert measure_empty (μ := μ)
      ext ζ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h hc
    have hμq : 0 < μ {ζ | (q : ℝ) < l ⬝ᵥ M.h ζ} := by
      refine lt_of_lt_of_le (pos_iff_ne_zero.2 hqpos) (measure_mono fun ζ hζ => hζ.2)
    obtain ⟨i0, hi0⟩ := hhit l hl q hμq
    have hcont : Continuous fun x' : Fin n → ℝ => l ⬝ᵥ (M.T *ᵥ x') :=
      continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)
    refine ⟨{x' | l ⬝ᵥ (M.T *ᵥ x') < q}, (isOpen_lt hcont continuous_const).mem_nhds hlq, ?_⟩
    filter_upwards [eventually_gt_atTop i0] with N hN x' hx'
    have hnf : ¬ feas M x' (s i0) := by
      rw [feas_iff]
      push Not
      refine ⟨l, hl, ?_⟩
      rw [dotProduct_sub]
      have : l ⬝ᵥ (M.T *ᵥ x') < q := hx'
      linarith
    rw [VSAA_top M hD s N x' hN hnf]
    exact lt_top_iff_ne_top.2 (ne_top_of_lt ha)

end SROSAAAux

namespace SROSAAAux
open TwoStageSRO.AsymOpt SROLP SROMeasAux

variable {n d r m mt : ℕ}

theorem eventually_on_compact {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {P : ℕ → (Fin n → ℝ) → Prop}
    (h : ∀ y ∈ K, ∃ U ∈ 𝓝 y, ∀ᶠ N in atTop, ∀ y' ∈ U, P N y') :
    ∀ᶠ N in atTop, ∀ y ∈ K, P N y := by
  choose U hU hev using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hU
  have hall : ∀ᶠ N in atTop, ∀ y ∈ t, ∀ y' ∈ U y.1 y.2, P N y' :=
    (Filter.eventually_all_finset t).2 fun y _ => hev y.1 y.2
  filter_upwards [hall] with N hN y hy
  obtain ⟨y0, hy0t, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact hN y0 hy0t y hyU

/-- A uniform margin above `v` on a compact set where `V* > v`. -/
theorem margin_on_compact {K : Set (Fin n → ℝ)} (hK : IsCompact K) (v : ℝ)
    {F : ℕ → (Fin n → ℝ) → EReal}
    (h : ∀ y ∈ K, ∃ a : ℝ, v < a ∧ ∃ U ∈ 𝓝 y, ∀ᶠ N in atTop, ∀ y' ∈ U, (a : EReal) < F N y') :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N in atTop, ∀ y ∈ K, ((v + η : ℝ) : EReal) < F N y := by
  classical
  choose a ha U hU hev using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hU
  set η : ℝ := if hne : t.Nonempty then t.inf' hne (fun y => a y.1 y.2 - v) else 1 with hη
  have hηpos : 0 < η := by
    rw [hη]
    split_ifs with hne
    · exact (Finset.lt_inf'_iff _).2 fun y _ => by linarith [ha y.1 y.2]
    · exact one_pos
  have hηle : ∀ y ∈ t, v + η ≤ a y.1 y.2 := by
    intro y hy
    have hne : t.Nonempty := ⟨y, hy⟩
    have : η ≤ a y.1 y.2 - v := by
      rw [hη, dif_pos hne]
      exact Finset.inf'_le _ hy
    linarith
  refine ⟨η, hηpos, ?_⟩
  have hall : ∀ᶠ N in atTop, ∀ y ∈ t, ∀ y' ∈ U y.1 y.2, (a y.1 y.2 : EReal) < F N y' :=
    (Filter.eventually_all_finset t).2 fun y _ => hev y.1 y.2
  filter_upwards [hall] with N hN y hy
  obtain ⟨y0, hy0t, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact lt_of_le_of_lt (EReal.coe_le_coe_iff.2 (hηle y0 hy0t)) (hN y0 hy0t y hyU)

/-- Deterministic core of SAA consistency on a fixed sample path. -/
theorem saa_det (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (s : ℕ → Fin d → ℝ)
    (hphi : ∀ x' : Fin n → ℚ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ i ∈ Finset.range N, phi M (fun k => (x' k : ℝ)) (s i)) atTop
        (𝓝 (∫ ζ, phi M (fun k => (x' k : ℝ)) ζ ∂μ)))
    (hhit : ∀ l ∈ extR M, ∀ q : ℚ, 0 < μ {ζ | (q : ℝ) < l ⬝ᵥ M.h ζ} →
      ∃ i, (q : ℝ) < l ⬝ᵥ M.h (s i))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ) (v : ℝ) (hv : vStar M μ = (v : EReal))
    (R0 : ℝ) (hR0 : 0 ≤ R0) (hopt : optSet M μ ⊆ Metric.closedBall xs R0)
    (hxsF : μ {ζ | ¬ feas M xs ζ} = 0)
    (hxsN : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, phi M xs (s i)) atTop
      (𝓝 (∫ ζ, phi M xs ζ ∂μ)))
    (hfeasxs : ∀ i, feas M xs (s i)) :
    Tendsto (fun N => vSAA M s N) atTop (𝓝 (v : EReal)) := by
  have epi := epi_liminf M hD μ hint s hphi hhit
  have hVxs : Vstar M μ xs = (v : EReal) := by
    rw [← hv]
    exact le_antisymm (le_iInf fun x => hxs (Set.mem_univ x)) (iInf_le _ _)
  have hΦxs : M.c ⬝ᵥ xs + ∫ ζ, phi M xs ζ ∂μ = v := by
    rw [Vstar_of_feas M hD μ hint xs hxsF] at hVxs
    exact EReal.coe_eq_coe_iff.1 hVxs
  have hVge : ∀ x, (v : EReal) ≤ Vstar M μ x := fun x => by rw [← hv]; exact iInf_le _ x
  -- the SAA objective at `x*` converges to `v*`
  have hVxsN : Tendsto (fun N => VSAA M s N xs) atTop (𝓝 (v : EReal)) := by
    have h1 : Tendsto (fun N => PhiN M s N xs) atTop (𝓝 v) := by
      rw [← hΦxs]; exact tendsto_const_nhds.add hxsN
    have h2 := (continuous_coe_real_ereal.tendsto _).comp h1
    refine h2.congr fun N => ?_
    simp only [Function.comp]
    exact (VSAA_eq_PhiN M hD s N xs fun i _ => hfeasxs i).symm
  set R1 := R0 + 1 with hR1
  -- `V* > v*` on the sphere of radius `R1`
  have hsph : ∀ y ∈ Metric.sphere xs R1, ∃ a : ℝ, v < a ∧ ∃ U ∈ 𝓝 y, ∀ᶠ N in atTop,
      ∀ y' ∈ U, (a : EReal) < VSAA M s N y' := by
    intro y hy
    have hyopt : y ∉ optSet M μ := fun h => by
      have := hopt h
      rw [Metric.mem_closedBall] at this
      rw [Metric.mem_sphere] at hy
      linarith
    have hlt : (v : EReal) < Vstar M μ y := by
      by_contra hle
      push Not at hle
      apply hyopt
      intro x _
      exact hle.trans (hVge x)
    obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    exact ⟨a, EReal.coe_lt_coe_iff.1 ha1, epi y a ha2⟩
  obtain ⟨η, hηpos, hmargin⟩ := margin_on_compact (isCompact_sphere xs R1) v hsph
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨a', ha'1, ha'2⟩ := EReal.lt_iff_exists_real_btwn.1 (hv ▸ ha : a < (v : EReal))
    have ha'v : a' < v := EReal.coe_lt_coe_iff.1 ha'2
    have hball : ∀ᶠ N in atTop, ∀ y ∈ Metric.closedBall xs R1, (a' : EReal) < VSAA M s N y :=
      eventually_on_compact (isCompact_closedBall xs R1) fun y _ =>
        epi y a' (lt_of_lt_of_le ha'2 (hVge y))
    have hxsev : ∀ᶠ N in atTop, VSAA M s N xs < ((v + η : ℝ) : EReal) :=
      hVxsN.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)))
    filter_upwards [hball, hmargin, hxsev, eventually_ge_atTop 1] with N hNb hNm hNxs hN1
    refine lt_of_lt_of_le ha'1 (le_iInf fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall xs R1
    · exact (hNb x hx).le
    · -- outside the ball, convexity and the margin on the sphere
      rw [Metric.mem_closedBall, not_le] at hx
      by_contra hlow
      push Not at hlow
      have hlow' : VSAA M s N x < ((v + η : ℝ) : EReal) :=
        lt_trans hlow (EReal.coe_lt_coe_iff.2 (by linarith))
      have hfx : ∀ i < N, feas M x (s i) := by
        intro i hi
        by_contra hnf
        rw [VSAA_top M hD s N x hi hnf] at hlow'
        exact absurd hlow' (not_lt.2 le_top)
      have hdist : 0 < dist x xs := lt_trans (by linarith) hx
      set t := R1 / dist x xs with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hdist.le
      have ht1 : t ≤ 1 := (div_le_one hdist).2 hx.le
      set y := (1 - t) • xs + t • x with hy
      have hyS : y ∈ Metric.sphere xs R1 := by
        rw [Metric.mem_sphere, dist_eq_norm]
        have : y - xs = t • (x - xs) := by rw [hy]; module
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← dist_eq_norm, ht,
          div_mul_cancel₀ _ hdist.ne']
      have hfy : ∀ i < N, feas M y (s i) := fun i hi =>
        feas_convex M (hfeasxs i) (hfx i hi) t ht0 ht1
      have h1 := hNm y hyS
      rw [VSAA_eq_PhiN M hD s N y hfy] at h1
      rw [VSAA_eq_PhiN M hD s N xs fun i _ => hfeasxs i] at hNxs
      rw [VSAA_eq_PhiN M hD s N x hfx] at hlow'
      have h1' := EReal.coe_lt_coe_iff.1 h1
      have h2' := EReal.coe_lt_coe_iff.1 hNxs
      have h3' := EReal.coe_lt_coe_iff.1 hlow'
      have hconv := PhiN_convex M s N xs x t ht0 ht1
      have : (1 - t) * PhiN M s N xs + t * PhiN M s N x < v + η := by
        have := mul_le_mul_of_nonneg_left h2'.le (by linarith : (0 : ℝ) ≤ 1 - t)
        have := mul_le_mul_of_nonneg_left h3'.le ht0
        rcases ht0.lt_or_eq with htp | htz
        · have := mul_lt_mul_of_pos_left h3' htp
          nlinarith
        · rw [← htz] at *
          simp only [sub_zero, one_mul, zero_mul, add_zero]
          exact h2'
      linarith
  · filter_upwards [hVxsN.eventually (gt_mem_nhds (hv ▸ hb : (v : EReal) < b))] with N hN
    exact lt_of_le_of_lt (iInf_le _ xs) hN

/-- Deterministic argmin consistency on a fixed sample path. -/
theorem argmin_det (M : Model n d r m mt) (hD : (stdPoly M.W M.q).Nonempty)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (s : ℕ → Fin d → ℝ)
    (hphi : ∀ x' : Fin n → ℚ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ i ∈ Finset.range N, phi M (fun k => (x' k : ℝ)) (s i)) atTop
        (𝓝 (∫ ζ, phi M (fun k => (x' k : ℝ)) ζ ∂μ)))
    (hhit : ∀ l ∈ extR M, ∀ q : ℚ, 0 < μ {ζ | (q : ℝ) < l ⬝ᵥ M.h ζ} →
      ∃ i, (q : ℝ) < l ⬝ᵥ M.h (s i))
    (v : ℝ) (hv : vStar M μ = (v : EReal))
    (hval : Tendsto (fun N => vSAA M s N) atTop (𝓝 (v : EReal)))
    (xh : ℕ → (Fin n → ℝ)) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ᶠ N in atTop, VSAA M s N (xh N) ≤ vSAA M s N + ((η N : ℝ) : EReal))
    (xb : Fin n → ℝ) (hxb : MapClusterPt xb atTop xh) : xb ∈ optSet M μ := by
  have hVge : ∀ x, (v : EReal) ≤ Vstar M μ x := fun x => by rw [← hv]; exact iInf_le _ x
  suffices h : Vstar M μ xb ≤ (v : EReal) by
    intro x _
    exact h.trans (hVge x)
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hav : v < a := EReal.coe_lt_coe_iff.1 ha1
  obtain ⟨U, hU, hev⟩ := epi_liminf M hD μ hint s hphi hhit xb a ha2
  set e := (a - v) / 2 with he
  have hepos : 0 < e := by rw [he]; linarith
  have h1 : ∀ᶠ N in atTop, vSAA M s N < ((v + e : ℝ) : EReal) :=
    hval.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith)))
  have h2 : ∀ᶠ N in atTop, η N < e := hη.eventually (gt_mem_nhds hepos)
  have hfreq := (mapClusterPt_iff_frequently.1 hxb) U hU
  obtain ⟨N, hN5, hN1, hN2, hN3, hN4⟩ :=
    (hfreq.and_eventually (hev.and (h1.and (h2.and hnear)))).exists
  have hlt' : vSAA M s N + ((η N : ℝ) : EReal) < (a : EReal) := by
    have : ((v + e : ℝ) : EReal) + ((e : ℝ) : EReal) = (a : EReal) := by
      rw [← EReal.coe_add]; congr 1; rw [he]; ring
    rw [← this]
    exact EReal.add_lt_add hN2 (EReal.coe_lt_coe_iff.2 hN3)
  have := hN1 (xh N) hN5
  exact lt_irrefl _ (lt_of_lt_of_le this (hN4.trans hlt'.le))

end SROSAAAux

namespace SROSAAAux
open TwoStageSRO.AsymOpt SROLP SROMeasAux

variable {n d r m mt : ℕ}

/-- Almost-sure SAA value and argmin consistency (King–Wets) for the two-stage problem. -/
theorem saa_main (M : Model n d r m mt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => vSAA M (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      ∀ (xh : ℕ → (Fin n → ℝ)) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) →
        (∀ᶠ N in atTop,
          VSAA M (fun i => ξ i ω) N (xh N) ≤ vSAA M (fun i => ξ i ω) N + ((η N : ℝ) : EReal)) →
        ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ := by
  classical
  have : IsProbabilityMeasure μ := by
    rw [← (hlaw 0).map_eq]; exact Measure.isProbabilityMeasure_map (hlaw 0).aemeasurable
  obtain ⟨xs, hxs⟩ := hA3.1
  have hVxs : Vstar M μ xs = vStar M μ :=
    le_antisymm (le_iInf fun x => hxs (Set.mem_univ x)) (iInf_le _ _)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, vStar M μ = (v : EReal) :=
    ⟨(vStar M μ).toReal, (EReal.coe_toReal hA2.1 hA2.2.1).symm⟩
  -- the dual polyhedron is nonempty (footnote 3)
  have hD : (stdPoly M.W M.q).Nonempty := by
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
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall xs).1 hA3.2
  have hopt : optSet M μ ⊆ Metric.closedBall xs (max R 0) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hxsF : μ {ζ | ¬ feas M xs ζ} = 0 := by
    by_contra h
    have := Vstar_of_not_feas M μ xs h
    rw [hVxs, hv] at this
    exact EReal.coe_ne_top v this
  have hint := hA2.2.2
  -- the almost-sure events
  have Ephi : ∀ᵐ ω ∂P, ∀ x' : Fin n → ℚ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ i ∈ Finset.range N, phi M (fun k => (x' k : ℝ)) (ξ i ω)) atTop
        (𝓝 (∫ ζ, phi M (fun k => (x' k : ℝ)) ζ ∂μ)) :=
    ae_all_iff.2 fun x' => slln_fun P μ ξ hind hlaw _ (phi_measurable M _)
      (phi_integrable M μ hint _)
  have Exs := slln_fun P μ ξ hind hlaw _ (phi_measurable M xs) (phi_integrable M μ hint xs)
  have Ehit0 : ∀ l : {l // l ∈ extR M}, ∀ q : ℚ, ∀ᵐ ω ∂P,
      0 < μ {ζ | (q : ℝ) < l.1 ⬝ᵥ M.h ζ} → ∃ i, (q : ℝ) < l.1 ⬝ᵥ M.h (ξ i ω) := by
    intro l q
    by_cases hp : 0 < μ {ζ | (q : ℝ) < l.1 ⬝ᵥ M.h ζ}
    · have hcont : Continuous fun ζ : Fin d → ℝ => l.1 ⬝ᵥ M.h ζ := by
        unfold Model.h
        exact continuous_const.dotProduct (continuous_const.add
          (continuous_const.matrix_mulVec continuous_id))
      have hmeas : MeasurableSet {ζ : Fin d → ℝ | (q : ℝ) < l.1 ⬝ᵥ M.h ζ} :=
        (isOpen_lt continuous_const hcont).measurableSet
      filter_upwards [hit_ae P μ ξ hind hlaw _ hmeas hp] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  have Ehit : ∀ᵐ ω ∂P, ∀ l ∈ extR M, ∀ q : ℚ, 0 < μ {ζ | (q : ℝ) < l ⬝ᵥ M.h ζ} →
      ∃ i, (q : ℝ) < l ⬝ᵥ M.h (ξ i ω) := by
    have := ae_all_iff.2 fun l => ae_all_iff.2 fun q => Ehit0 l q
    filter_upwards [this] with ω hω l hl q hq
    exact hω ⟨l, hl⟩ q hq
  have Efeas : ∀ᵐ ω ∂P, ∀ i, feas M xs (ξ i ω) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ ζ ∂(P.map (ξ i)), feas M xs ζ := by
      rw [(hlaw i).map_eq, ae_iff]; exact hxsF
    exact ae_of_ae_map (hlaw i).aemeasurable this
  filter_upwards [Ephi, Exs, Ehit, Efeas] with ω h1 h2 h3 h4
  have hval := saa_det M hD μ hint (fun i => ξ i ω) h1 h3 xs hxs v hv (max R 0)
    (le_max_right _ _) hopt hxsF h2 h4
  refine ⟨hv ▸ hval, fun xh η hη hnear xb hxb => ?_⟩
  exact argmin_det M hD μ hint (fun i => ξ i ω) h1 h3 v hv hval xh η hη hnear xb hxb

end SROSAAAux

open TwoStageSRO.AsymOpt SROSAAAux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ)) :
    ∀ᵐ ω ∂P, ∀ (xh : ℕ → (Fin n → ℝ)) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) →
      (∀ᶠ N in atTop,
        VSAA M (fun i => ξ i ω) N (xh N) ≤ vSAA M (fun i => ξ i ω) N + ((η N : ℝ) : EReal)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ :=
  (saa_main M P μ ξ hind hlaw hA2 hA3).mono fun _ h => h.2

