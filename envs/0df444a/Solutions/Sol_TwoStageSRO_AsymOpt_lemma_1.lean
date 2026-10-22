-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:34:54.331985+00:00
-- url     : https://prove2.me/submissions/aa56724e-5439-4b43-9182-99cdeacdef42

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

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

namespace SROLemma9Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

theorem face_subset_Xi (M : Model n d r m mt) (I : Finset (Fin mt)) : face M I ⊆ Xi M :=
  fun _ h => h.1

/-- A point of the relative interior can be pushed slightly beyond itself, away from any other
point of the set. -/
theorem extend_of_mem_intrinsicInterior {d : ℕ} {F : Set (Fin d → ℝ)} {x x' : Fin d → ℝ}
    (hx : x ∈ intrinsicInterior ℝ F) (hx' : x' ∈ F) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - x') ∈ F := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hx
  have hyF : (y : Fin d → ℝ) ∈ affineSpan ℝ F := y.2
  have hx'F : x' ∈ affineSpan ℝ F := subset_affineSpan ℝ F hx'
  have hmem : ∀ t : ℝ, (y : Fin d → ℝ) + t • ((y : Fin d → ℝ) - x') ∈ affineSpan ℝ F := by
    intro t
    have := AffineMap.lineMap_mem (1 + t) hx'F hyF
    convert this using 1
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_smul, one_smul, smul_sub]
    abel
  let γ : ℝ → affineSpan ℝ F := fun t => ⟨(y : Fin d → ℝ) + t • ((y : Fin d → ℝ) - x'), hmem t⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = y := by
    apply Subtype.ext
    simp [γ]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ interior ((↑) ⁻¹' F : Set (affineSpan ℝ F)) :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact isOpen_interior.mem_nhds hy)
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have h2 : γ t ∈ ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := interior_subset ht
  exact ⟨t, htpos, h2⟩

/-- Points in the relative interior of the same face have the same active constraints. -/
theorem active_transfer (M : Model n d r m mt) {F : Set (Fin d → ℝ)} (hF : IsFace M F)
    {zhat zbar : Fin d → ℝ} (hzhat : zhat ∈ intrinsicInterior ℝ F)
    (hzbar : zbar ∈ intrinsicInterior ℝ F) (k : Fin mt) (hk : zbar ∈ hyperplane M k) :
    zhat ∈ hyperplane M k := by
  obtain ⟨-, I, rfl⟩ := hF
  have hzhatF : zhat ∈ face M I := intrinsicInterior_subset hzhat
  obtain ⟨t, ht, hw⟩ := extend_of_mem_intrinsicInterior hzbar hzhatF
  have h1 := (face_subset_Xi M I hw) k
  have h2 := (face_subset_Xi M I hzhatF) k
  simp only [hyperplane, Set.mem_ofPred_eq] at hk ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub] at h1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
  rw [hk] at h1
  have : t * (M.g0 k - (M.G *ᵥ zhat) k) ≥ 0 := by linarith
  have h3 : M.g0 k - (M.G *ᵥ zhat) k ≥ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  linarith

/-- One inclusion of Lemma 9: translating `B(ẑ, ε) ∩ Ξ` by `z̄ - ẑ` lands in `B(z̄, ε) ∩ Ξ`
whenever every constraint active at `z̄` is active at `ẑ` and `ε ≤ ∆_Ξ(z̄)`. -/
theorem translate_subset (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {zhat zbar : Fin d → ℝ} (hzbarX : zbar ∈ Xi M)
    (hact : ∀ k, zbar ∈ hyperplane M k → zhat ∈ hyperplane M k)
    (ε : ℝ) (hεr : (ε : EReal) ≤ radius M p zbar) (ζ : Fin d → ℝ)
    (hζ : ζ ∈ ball p zhat ε ∩ Xi M) : ζ + (zbar - zhat) ∈ ball p zbar ε ∩ Xi M := by
  obtain ⟨hb, hx⟩ := hζ
  have hb' : ‖WithLp.toLp p (ζ - zhat)‖ ≤ ε := hb
  have hdiff : ζ + (zbar - zhat) - zbar = ζ - zhat := by abel
  refine ⟨?_, ?_⟩
  · show ‖WithLp.toLp p (ζ + (zbar - zhat) - zbar)‖ ≤ ε
    rw [hdiff]; exact hb'
  · intro k
    have hxk := hx k
    have hzk := hzbarX k
    rw [Matrix.mulVec_add, Matrix.mulVec_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hk : zbar ∈ hyperplane M k
    · have hk' := hact k hk
      simp only [hyperplane, Set.mem_ofPred_eq] at hk hk'
      linarith
    · by_contra hcon
      push Not at hcon
      obtain ⟨s, hs⟩ : ∃ s, s = (M.G *ᵥ zbar) k - M.g0 k := ⟨_, rfl⟩
      obtain ⟨a, ha⟩ : ∃ a, a = (M.G *ᵥ (ζ - zhat)) k := ⟨_, rfl⟩
      have haeq : a = (M.G *ᵥ ζ) k - (M.G *ᵥ zhat) k := by
        rw [ha, Matrix.mulVec_sub]; rfl
      have hspos : 0 < s := by
        rcases (show 0 ≤ s by linarith).lt_or_eq with h | h
        · exact h
        · exfalso; apply hk; simp only [hyperplane, Set.mem_ofPred_eq]; linarith
      have hsa : s + a < 0 := by linarith
      have ha0 : a < 0 := by linarith
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -s / a := ⟨_, rfl⟩
      have hcpos : 0 < c := by rw [hc]; exact div_pos_of_neg_of_neg (by linarith) ha0
      have hc1 : c < 1 := by
        rw [hc, div_lt_one_of_neg ha0]; linarith
      have hca : c * a = -s := by rw [hc, div_mul_cancel₀ _ ha0.ne]
      have hw : zbar + c • (ζ - zhat) ∈ hyperplane M k := by
        simp only [hyperplane, Set.mem_ofPred_eq, Matrix.mulVec_add, Matrix.mulVec_smul,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← ha]
        linarith
      have hv0 : 0 < ‖WithLp.toLp p (ζ - zhat)‖ := by
        refine norm_pos_iff.2 fun h0 => ?_
        have : ζ - zhat = 0 := by
          have := congrArg WithLp.ofLp h0
          simpa using this
        rw [this, Matrix.mulVec_zero] at ha
        simp at ha
        linarith
      have hle : radius M p zbar ≤
          ((‖WithLp.toLp p (zbar + c • (ζ - zhat) - zbar)‖ : ℝ) : EReal) := by
        unfold radius
        exact iInf₂_le_of_le k hk (iInf₂_le _ hw)
      have hlt : ‖WithLp.toLp p (zbar + c • (ζ - zhat) - zbar)‖ < ε := by
        rw [add_sub_cancel_left, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hcpos]
        calc c * ‖WithLp.toLp p (ζ - zhat)‖ < 1 * ‖WithLp.toLp p (ζ - zhat)‖ :=
              mul_lt_mul_of_pos_right hc1 hv0
          _ ≤ ε := by rw [one_mul]; exact hb'
      exact lt_irrefl _ (lt_of_le_of_lt (hεr.trans hle) (EReal.coe_lt_coe_iff.2 hlt))

/-- On a minimal face every constraint function is constant. -/
theorem minimalFace_const (M : Model n d r m mt) {F : Set (Fin d → ℝ)} (hF : IsMinimalFace M F)
    {a b : Fin d → ℝ} (ha : a ∈ F) (hb : b ∈ F) (k : Fin mt) :
    (M.G *ᵥ a) k = (M.G *ᵥ b) k := by
  classical
  obtain ⟨⟨hne, I, rfl⟩, hmin⟩ := hF
  -- reduce to the case `(G a)_k < (G b)_k`
  suffices key : ∀ a b : Fin d → ℝ, a ∈ face M I → b ∈ face M I → ∀ k,
      ¬ (M.G *ᵥ a) k < (M.G *ᵥ b) k by
    rcases lt_trichotomy ((M.G *ᵥ a) k) ((M.G *ᵥ b) k) with h | h | h
    · exact absurd h (key a b ha hb k)
    · exact h
    · exact absurd h (key b a hb ha k)
  intro a b ha hb k hlt
  set dv := a - b with hdv
  have hGd : ∀ j, (M.G *ᵥ dv) j = (M.G *ᵥ a) j - (M.G *ᵥ b) j := by
    intro j; rw [hdv, Matrix.mulVec_sub]; rfl
  set J := Finset.univ.filter (fun j => (M.G *ᵥ dv) j < 0) with hJ
  have hJne : J.Nonempty := ⟨k, by simp [hJ, hGd]; linarith⟩
  obtain ⟨j0, hj0J, hj0min⟩ := J.exists_min_image
    (fun j => ((M.G *ᵥ a) j - M.g0 j) / (-(M.G *ᵥ dv) j)) hJne
  have hj0neg : (M.G *ᵥ dv) j0 < 0 := by simpa [hJ] using hj0J
  set t := ((M.G *ᵥ a) j0 - M.g0 j0) / (-(M.G *ᵥ dv) j0) with ht
  have hax := ha.1
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hax j0]) (by linarith)
  set c := a + t • dv with hc
  have hGc : ∀ j, (M.G *ᵥ c) j = (M.G *ᵥ a) j + t * (M.G *ᵥ dv) j := by
    intro j; rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul]; rfl
  have hcX : c ∈ Xi M := by
    intro j
    rw [hGc]
    by_cases hj : (M.G *ᵥ dv) j < 0
    · have h1 : t ≤ ((M.G *ᵥ a) j - M.g0 j) / (-(M.G *ᵥ dv) j) := hj0min j (by simp [hJ, hj])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push Not at hj
      have := hax j
      nlinarith
  have hcI : ∀ i ∈ I, (M.G *ᵥ c) i = M.g0 i := by
    intro i hi
    rw [hGc, hGd, ha.2 i hi, hb.2 i hi]
    ring
  have hcj0 : (M.G *ᵥ c) j0 = M.g0 j0 := by
    have e : ((M.G *ᵥ a) j0 - M.g0 j0) / -(M.G *ᵥ dv) j0 * (M.G *ᵥ dv) j0 =
        -((M.G *ᵥ a) j0 - M.g0 j0) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hj0neg.ne]; ring
    rw [hGc, ht, e]
    ring
  have hF' : IsFace M (face M (insert j0 I)) := by
    refine ⟨⟨c, hcX, ?_⟩, insert j0 I, rfl⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with h | h
    · rw [h]; exact hcj0
    · exact hcI i h
  have hsub : face M (insert j0 I) ⊆ face M I := fun z hz =>
    ⟨hz.1, fun i hi => hz.2 i (Finset.mem_insert_of_mem hi)⟩
  have heq := hmin _ hF' hsub
  have ha' : a ∈ face M (insert j0 I) := heq ▸ ha
  have hb' : b ∈ face M (insert j0 I) := heq ▸ hb
  have h1 := ha'.2 j0 (Finset.mem_insert_self _ _)
  have h2 := hb'.2 j0 (Finset.mem_insert_self _ _)
  rw [hGd, h1, h2, sub_self] at hj0neg
  exact lt_irrefl _ hj0neg

end SROLemma9Aux

namespace SROLemma2Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

/-- The worst-case cost of an affine policy over a (bounded) set `B(ẑ, ε) ∩ S` is finite. -/
theorem robCost_affine_lt_top (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : Fin d → ℝ) (ε : ℝ) (S : Set (Fin d → ℝ)) (y0 : Fin r → ℝ)
    (Y : Matrix (Fin r) (Fin d) ℝ) :
    robCost M (ball p z ε ∩ S) (fun ζ => y0 + Y *ᵥ ζ) < ⊤ := by
  let K : Set (Fin d → ℝ) :=
    (fun u : PiLp p (fun _ : Fin d => ℝ) => z + WithLp.ofLp u) ''
      Metric.closedBall (0 : PiLp p (fun _ : Fin d => ℝ)) ε
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image (continuous_const.add (PiLp.continuous_ofLp p _))
  have hsub : ball p z ε ⊆ K := by
    intro ζ hζ
    refine ⟨WithLp.toLp p (ζ - z), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]; exact hζ
    · simp
  have hg : Continuous fun ζ : Fin d → ℝ => M.q ⬝ᵥ (y0 + Y *ᵥ ζ) :=
    continuous_const.dotProduct (continuous_const.add (continuous_const.matrix_mulVec
      continuous_id))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hg.continuousOn
  have : robCost M (ball p z ε ∩ S) (fun ζ => y0 + Y *ᵥ ζ) ≤ (B : EReal) := by
    unfold robCost
    refine iSup₂_le fun ζ hζ => ?_
    exact EReal.coe_le_coe_iff.2 (hB ⟨ζ, hsub hζ.1, rfl⟩)
  exact lt_of_le_of_lt this (EReal.coe_lt_top B)

end SROLemma2Aux

namespace SROL1Aux
open TwoStageSRO.AsymOpt SROLP SROEq3Aux SROLemma9Aux SROLemma2Aux

variable {n d r m mt : ℕ}

/-- A single linear decision rule with recourse matrix in `C` is robustly feasible for `x` on
`B(ζ, ρ) ∩ Ξ`. -/
def Good (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (C : Set (Matrix (Fin r) (Fin d) ℝ))
    (x : Fin n → ℝ) (ζ : Fin d → ℝ) (ρ : ℝ) : Prop :=
  ∃ y0 : Fin r → ℝ, ∃ Y ∈ C, robFeas M x (ball p ζ ρ ∩ Xi M) (fun z => y0 + Y *ᵥ z)

theorem good_mono (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) (x : Fin n → ℝ) {ζ ζ' : Fin d → ℝ} {ρ ρ' : ℝ}
    (hg : Good M p C x ζ' ρ') (h : ‖WithLp.toLp p (ζ - ζ')‖ + ρ ≤ ρ') : Good M p C x ζ ρ := by
  obtain ⟨y0, Y, hY, hrob⟩ := hg
  refine ⟨y0, Y, hY, fun z hz => hrob z ⟨?_, hz.2⟩⟩
  have hz1 : ‖WithLp.toLp p (z - ζ)‖ ≤ ρ := hz.1
  show ‖WithLp.toLp p (z - ζ')‖ ≤ ρ'
  have e : WithLp.toLp p (z - ζ') = WithLp.toLp p (z - ζ) + WithLp.toLp p (ζ - ζ') := by
    rw [← WithLp.toLp_add]; congr 1; abel
  rw [e]
  exact (norm_add_le _ _).trans (by linarith)

/-- Midpoint contraction of a robustly feasible rule towards a point with a feasible recourse. -/
theorem good_mid (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) (x : Fin n → ℝ) {ζb ζdd ζ : Fin d → ℝ} {ρA ρ : ℝ}
    (hg : Good M p C x ζb ρA) {ydd : Fin r → ℝ} (hfeas : M.h ζdd ≤ M.T *ᵥ x + M.W *ᵥ ydd)
    (hin : ∀ ζ' ∈ ball p ζ ρ ∩ Xi M, (2 : ℝ) • ζ' - ζdd ∈ ball p ζb ρA ∩ Xi M) :
    Good M p C x ζ ρ := by
  obtain ⟨y0, Y, hY, hrob⟩ := hg
  refine ⟨(1/2 : ℝ) • (y0 + ydd - Y *ᵥ ζdd), Y, hY, fun ζ' hζ' => ?_⟩
  have hA := hrob _ (hin ζ' hζ')
  intro j
  have hAj := hA j
  have hBj := hfeas j
  simp only [Model.h, Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hAj hBj ⊢
  linarith

theorem segment (M : Model n d r m mt) {J : Finset (Fin mt)} {ζ : Fin d → ℝ}
    (hζ : ζ ∈ face M J) {δ : ℝ} (hδ0 : 0 ≤ δ) (hB : ∀ j ∉ J, δ < (M.G *ᵥ ζ) j - M.g0 j)
    (e : Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t) (heJ : ∀ j ∈ J, (M.G *ᵥ e) j = 0)
    (hcond : ∀ j, (M.G *ᵥ e) j < 0 → t * (-(M.G *ᵥ e) j) ≤ (M.G *ᵥ ζ) j - M.g0 j - δ) :
    ζ + t • e ∈ face M J ∧ ∀ j ∉ J, δ ≤ (M.G *ᵥ (ζ + t • e)) j - M.g0 j := by
  have hlin : ∀ j, (M.G *ᵥ (ζ + t • e)) j = (M.G *ᵥ ζ) j + t * (M.G *ᵥ e) j := by
    intro j; rw [Matrix.mulVec_add, Matrix.mulVec_smul]; rfl
  have hslack : ∀ j ∉ J, δ ≤ (M.G *ᵥ (ζ + t • e)) j - M.g0 j := by
    intro j hj
    rw [hlin]
    by_cases hneg : (M.G *ᵥ e) j < 0
    · have := hcond j hneg
      linarith
    · push Not at hneg
      have := hB j hj
      nlinarith
  refine ⟨⟨fun j => ?_, fun j hj => ?_⟩, hslack⟩
  · by_cases hj : j ∈ J
    · rw [hlin, heJ j hj, mul_zero, add_zero]; exact hζ.1 j
    · have := hslack j hj; linarith
  · rw [hlin, heJ j hj, mul_zero, add_zero]; exact hζ.2 j hj

/-- The system describing the face `face M S` in `ζ`-space. -/
noncomputable def faceMat (M : Model n d r m mt) (S : Finset (Fin mt)) :
    Matrix (Fin mt ⊕ Fin mt) (Fin d) ℝ :=
  fun row => match row with
  | Sum.inl k => M.G k
  | Sum.inr k => if k ∈ S then -M.G k else 0

noncomputable def faceRhs (M : Model n d r m mt) (S : Finset (Fin mt)) : Fin mt ⊕ Fin mt → ℝ :=
  fun row => match row with
  | Sum.inl k => M.g0 k
  | Sum.inr k => if k ∈ S then -M.g0 k else 0

theorem faceMat_mulVec (M : Model n d r m mt) (S : Finset (Fin mt)) (z : Fin d → ℝ) :
    (∀ k, (faceMat M S *ᵥ z) (Sum.inl k) = (M.G *ᵥ z) k) ∧
    (∀ k, (faceMat M S *ᵥ z) (Sum.inr k) = if k ∈ S then -(M.G *ᵥ z) k else 0) := by
  refine ⟨fun k => rfl, fun k => ?_⟩
  by_cases hk : k ∈ S
  · simp [faceMat, hk, mulVec, dotProduct]
  · simp [faceMat, hk, mulVec, dotProduct]

theorem faceMat_feas (M : Model n d r m mt) (S : Finset (Fin mt)) (z : Fin d → ℝ) :
    faceRhs M S ≤ faceMat M S *ᵥ z ↔ z ∈ face M S := by
  have hev := faceMat_mulVec M S z
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · have := h (Sum.inl k); rw [hev.1 k] at this; exact this
    · have h1 := h (Sum.inl k); rw [hev.1 k] at h1
      have h2 := h (Sum.inr k); rw [hev.2 k] at h2
      simp only [faceRhs, hk, if_true] at h2 h1
      linarith
  · intro hz
    rintro (k | k)
    · rw [hev.1 k]; exact hz.1 k
    · rw [hev.2 k]
      by_cases hk : k ∈ S
      · simp only [faceRhs, hk, if_true]; linarith [hz.2 k hk]
      · simp [faceRhs, hk]

/-- **[A5] ⇒ [A6]** -/
theorem A5_to_A6 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : A5 M p → A6 M p := by
  classical
  rintro ⟨x, εb, hεb, ha, hb⟩
  have hrec : ∀ ζ ∈ Xi M, ∃ y, M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y := by
    intro ζ hζ
    by_contra hno
    push Not at hno
    have := ha ζ hζ
    unfold Q at this
    rw [sInf_eq_top.2 (by rintro _ ⟨y, hy, rfl⟩; exact absurd hy (hno y))] at this
    exact lt_irrefl _ this
  -- the finite set of recourse matrices
  let Ysel : Set (Fin d → ℝ) → Matrix (Fin r) (Fin d) ℝ := fun F =>
    if h : IsMinimalFace M F then Classical.choose (hb F h) else 0
  set C : Set (Matrix (Fin r) (Fin d) ℝ) :=
    Set.range (fun I : Finset (Fin mt) => Ysel (face M I)) with hCdef
  have hCfin : C.Finite := Set.finite_range _
  have hmin_good : ∀ I : Finset (Fin mt), IsMinimalFace M (face M I) →
      ∀ ζ ∈ face M I, Good M p C x ζ εb := by
    intro I hI ζ hζ
    have hspec := Classical.choose_spec (hb (face M I) hI)
    have hYsel : Ysel (face M I) = Classical.choose (hb (face M I) hI) := dif_pos hI
    have h1 := hspec ζ hζ
    unfold QC at h1
    rw [iInf_lt_iff] at h1
    obtain ⟨yY, h1⟩ := h1
    rw [iInf_lt_iff] at h1
    obtain ⟨⟨hY, hrob⟩, -⟩ := h1
    refine ⟨yY.1, yY.2, ⟨I, ?_⟩, hrob⟩
    show Ysel (face M I) = yY.2
    rw [hYsel]
    exact (Set.mem_singleton_iff.1 hY).symm
  -- constants
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
  -- Hoffman constants and gaps for the faces
  have hS : ∀ S : Finset (Fin mt), ∃ θS cS : ℝ, 0 ≤ θS ∧ 0 < cS ∧
      ((∃ z, faceRhs M S ≤ faceMat M S *ᵥ z) →
        ∀ z0 : Fin d → ℝ, ∀ ρ : ℝ, 0 ≤ ρ → (∀ i, faceRhs M S i - (faceMat M S *ᵥ z0) i ≤ ρ) →
          ∃ z, faceRhs M S ≤ faceMat M S *ᵥ z ∧ ∀ k, |z k - z0 k| ≤ θS * ρ) ∧
      ((¬ ∃ z, faceRhs M S ≤ faceMat M S *ᵥ z) →
        ∀ z0 : Fin d → ℝ, ∃ i, cS ≤ faceRhs M S i - (faceMat M S *ᵥ z0) i) := by
    intro S
    by_cases hfe : ∃ z, faceRhs M S ≤ faceMat M S *ᵥ z
    · obtain ⟨θS, hθS, hH⟩ := hoffman (faceMat M S) (faceRhs M S) hfe
      exact ⟨θS, 1, hθS, one_pos, fun _ => hH, fun h => absurd hfe h⟩
    · obtain ⟨cS, hcS, hG⟩ := infeasible_gap (faceMat M S) (faceRhs M S) hfe
      exact ⟨0, cS, le_rfl, hcS, fun h => absurd h hfe, fun _ => hG⟩
  choose θS cS hθS hcS hHoff hGap using hS
  set θ : ℝ := ∑ S : Finset (Fin mt), θS S with hθ
  have hθ0 : 0 ≤ θ := Finset.sum_nonneg fun S _ => hθS S
  have hθle : ∀ S, θS S ≤ θ := fun S =>
    Finset.single_le_sum (fun S _ => hθS S) (Finset.mem_univ S)
  set c : ℝ := Finset.univ.inf' ⟨∅, Finset.mem_univ _⟩ cS with hc
  have hcpos : 0 < c := (Finset.lt_inf'_iff _).2 fun S _ => hcS S
  have hcle : ∀ S, c ≤ cS S := fun S => Finset.inf'_le _ (Finset.mem_univ S)
  -- main induction over the faces, from the smallest ones up
  have main : ∀ nn : ℕ, ∀ J : Finset (Fin mt), mt - J.card = nn →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ ∈ face M J, Good M p C x ζ ρ := by
    intro nn
    induction nn using Nat.strong_induction_on with
    | _ nn ih =>
    intro J hJcard
    by_cases hne : (face M J).Nonempty
    swap
    · exact ⟨1, one_pos, fun ζ hζ => absurd ⟨ζ, hζ⟩ hne⟩
    by_cases hmin : IsMinimalFace M (face M J)
    · exact ⟨εb, hεb, hmin_good J hmin⟩
    -- a direction inside the face along which some constraint decreases
    obtain ⟨dv, k, hdJ, hdk⟩ : ∃ dv : Fin d → ℝ, ∃ k : Fin mt,
        (∀ j ∈ J, (M.G *ᵥ dv) j = 0) ∧ (M.G *ᵥ dv) k < 0 := by
      have hface : IsFace M (face M J) := ⟨hne, J, rfl⟩
      simp only [IsMinimalFace, not_and, not_forall] at hmin
      obtain ⟨F', hF', hsub, hneq⟩ := hmin hface
      obtain ⟨⟨b, hbF⟩, I', rfl⟩ := hF'
      obtain ⟨a, haJ, haI⟩ : ∃ a ∈ face M J, a ∉ face M I' := by
        by_contra hcon
        push Not at hcon
        exact hneq (Set.Subset.antisymm hsub hcon)
      obtain ⟨k, hkI, hka⟩ : ∃ k ∈ I', (M.G *ᵥ a) k ≠ M.g0 k := by
        by_contra hcon
        push Not at hcon
        exact haI ⟨haJ.1, hcon⟩
      have hbJ := hsub hbF
      refine ⟨b - a, k, fun j hj => ?_, ?_⟩
      · rw [Matrix.mulVec_sub]
        simp only [Pi.sub_apply]
        rw [hbJ.2 j hj, haJ.2 j hj, sub_self]
      · rw [Matrix.mulVec_sub]
        simp only [Pi.sub_apply]
        rw [hbF.2 k hkI]
        have := haJ.1 k
        exact sub_neg.2 (lt_of_le_of_ne this (Ne.symm hka))
    have hkJ : k ∉ J := fun h => by rw [hdJ k h] at hdk; exact lt_irrefl _ hdk
    -- the induction hypothesis on the larger index sets
    have hIH : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧ (j ∉ J → ∀ ζ ∈ face M (insert j J), Good M p C x ζ ρ) := by
      intro j
      by_cases hj : j ∈ J
      · exact ⟨1, one_pos, fun h => absurd hj h⟩
      · have hlt : J.card < mt := by
          have := Finset.card_lt_univ_of_notMem hj
          simpa using this
        obtain ⟨ρ, hρ, hgood⟩ := ih (mt - (insert j J).card)
          (by rw [Finset.card_insert_of_notMem hj]; omega) (insert j J) rfl
        exact ⟨ρ, hρ, fun _ => hgood⟩
    choose ρIH hρIH hgoodIH using hIH
    set ρmin : ℝ := Finset.univ.inf' ⟨k, Finset.mem_univ _⟩ ρIH with hρmin
    have hρmin : 0 < ρmin := (Finset.lt_inf'_iff _).2 fun j _ => hρIH j
    have hρminle : ∀ j, ρmin ≤ ρIH j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
    set δ : ℝ := min (c / 2) (ρmin / (2 * (Kd * θ) + 2)) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (div_pos hρmin (by positivity))
    have hδc : δ < c := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδρ : Kd * (θ * δ) ≤ ρmin / 2 := by
      have h1 : δ ≤ ρmin / (2 * (Kd * θ) + 2) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      have : 0 ≤ Kd * θ := by positivity
      nlinarith
    set ρJ : ℝ := min (ρmin / 4) (δ / (2 * K)) with hρJ
    have hρJpos : 0 < ρJ := lt_min (by linarith) (div_pos hδpos (by linarith))
    have hρJ1 : ρJ ≤ ρmin / 4 := min_le_left _ _
    have hρJ2 : 2 * K * ρJ ≤ δ := by
      have h1 : ρJ ≤ δ / (2 * K) := min_le_right _ _
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    -- Case A: close to a smaller face
    have caseA : ∀ ζ ∈ face M J, ∀ j ∉ J, (M.G *ᵥ ζ) j - M.g0 j ≤ δ →
        Good M p C x ζ (ρmin / 2) := by
      intro ζ hζ j hj hsj
      have hev := faceMat_mulVec M (insert j J) ζ
      have hviol : ∀ i, faceRhs M (insert j J) i - (faceMat M (insert j J) *ᵥ ζ) i ≤ δ := by
        rintro (kk | kk)
        · rw [hev.1 kk]; simp only [faceRhs]; linarith [hζ.1 kk]
        · rw [hev.2 kk]
          by_cases hk : kk ∈ insert j J
          · simp only [faceRhs, hk, if_true]
            rcases Finset.mem_insert.1 hk with h | h
            · subst h; linarith
            · rw [hζ.2 kk h]; linarith
          · simp [faceRhs, hk]; linarith
      have hfe : ∃ z, faceRhs M (insert j J) ≤ faceMat M (insert j J) *ᵥ z := by
        by_contra hfe
        obtain ⟨i, hi⟩ := hGap _ hfe ζ
        have := hviol i
        have := hcle (insert j J)
        linarith
      obtain ⟨ζ', hζ', hdist⟩ := hHoff _ hfe ζ δ hδpos.le hviol
      have hζ'F : ζ' ∈ face M (insert j J) := (faceMat_feas M _ ζ').1 hζ'
      have hnorm : ‖WithLp.toLp p (ζ - ζ')‖ ≤ Kd * (θ * δ) := by
        refine norm_le_of_coord p _ _ (mul_nonneg hθ0 hδpos.le) fun i => ?_
        have := hdist i
        calc |(ζ - ζ') i| = |ζ' i - ζ i| := by rw [Pi.sub_apply, abs_sub_comm]
          _ ≤ θS (insert j J) * δ := this
          _ ≤ θ * δ := mul_le_mul_of_nonneg_right (hθle _) hδpos.le
      refine good_mono M p C x (hgoodIH j hj ζ' hζ'F) ?_
      have := hρminle j
      linarith
    refine ⟨ρJ, hρJpos, fun ζ hζ => ?_⟩
    by_cases hA : ∃ j ∉ J, (M.G *ᵥ ζ) j - M.g0 j ≤ δ
    · obtain ⟨j, hj, hsj⟩ := hA
      exact good_mono M p C x (caseA ζ hζ j hj hsj) (by simp; linarith)
    push Not at hA
    -- Case B: far from smaller faces; reflect along `dv`
    have Bstep : ∀ (e : Fin d → ℝ) (t0 : ℝ) (j0 : Fin mt), 0 ≤ t0 →
        (∀ j ∈ J, (M.G *ᵥ e) j = 0) → j0 ∉ J →
        t0 * (-(M.G *ᵥ e) j0) = (M.G *ᵥ ζ) j0 - M.g0 j0 - δ →
        (∀ j, (M.G *ᵥ e) j < 0 → t0 * (-(M.G *ᵥ e) j) ≤ (M.G *ᵥ ζ) j - M.g0 j - δ) →
        (∀ j, 0 < (M.G *ᵥ e) j → t0 * (M.G *ᵥ e) j ≤ (M.G *ᵥ ζ) j - M.g0 j - δ) →
        Good M p C x ζ ρJ := by
      intro e t0 j0 ht0 heJ hj0 hj0eq hfwd hbwd
      obtain ⟨hζbF, hζbS⟩ := segment M hζ hδpos.le hA e t0 ht0 heJ hfwd
      have hmeJ : ∀ j ∈ J, (M.G *ᵥ (-e)) j = 0 := fun j hj => by
        rw [Matrix.mulVec_neg, Pi.neg_apply, heJ j hj, neg_zero]
      obtain ⟨hζdF, -⟩ := segment M hζ hδpos.le hA (-e) t0 ht0 hmeJ (fun j hj => by
        rw [Matrix.mulVec_neg, Pi.neg_apply, neg_neg]
        rw [Matrix.mulVec_neg, Pi.neg_apply] at hj
        exact hbwd j (by linarith))
      have hζb_j0 : (M.G *ᵥ (ζ + t0 • e)) j0 - M.g0 j0 ≤ δ := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      have hgb := caseA _ hζbF j0 hj0 hζb_j0
      obtain ⟨ydd, hydd⟩ := hrec _ hζdF.1
      refine good_mid M p C x hgb hydd fun ζ' hζ' => ?_
      have hζ'b : ‖WithLp.toLp p (ζ' - ζ)‖ ≤ ρJ := hζ'.1
      have hrw : (2 : ℝ) • ζ' - (ζ + t0 • -e) = (ζ + t0 • e) + (2 : ℝ) • (ζ' - ζ) := by
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        ring
      rw [hrw]
      refine ⟨?_, fun j => ?_⟩
      · show ‖WithLp.toLp p (ζ + t0 • e + (2 : ℝ) • (ζ' - ζ) - (ζ + t0 • e))‖ ≤ ρmin / 2
        rw [add_sub_cancel_left, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_two]
        linarith
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        by_cases hj : j ∈ J
        · rw [hζbF.2 j hj, hζ.2 j hj]
          have := hζ'.2 j
          linarith
        · have h1 := hζbS j hj
          have h2 : |(M.G *ᵥ (ζ' - ζ)) j| ≤ K * ρJ :=
            (G_bound M p (ζ' - ζ) j).trans (mul_le_mul_of_nonneg_left hζ'b (by linarith))
          rw [Matrix.mulVec_sub] at h2
          simp only [Pi.sub_apply] at h2
          have h3 := neg_abs_le ((M.G *ᵥ ζ') j - (M.G *ᵥ ζ) j)
          linarith
    -- thresholds in both directions
    set Tp := Finset.univ.filter (fun j => (M.G *ᵥ dv) j < 0) with hTp
    have hTpne : Tp.Nonempty := ⟨k, by simp [hTp, hdk]⟩
    have hTpJ : ∀ j ∈ Tp, j ∉ J := fun j hj hjJ => by
      simp only [hTp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hdJ j hjJ] at hj; exact lt_irrefl _ hj
    set ratp : Fin mt → ℝ := fun j => ((M.G *ᵥ ζ) j - M.g0 j - δ) / (-(M.G *ᵥ dv) j)
      with hratp
    set tp := Tp.inf' hTpne ratp with htp
    obtain ⟨jp, hjpT, hjpeq⟩ := Finset.exists_mem_eq_inf' hTpne ratp
    have hjpneg : (M.G *ᵥ dv) jp < 0 := by simpa [hTp] using hjpT
    have htp0 : 0 ≤ tp := by
      rw [← htp] at hjpeq
      rw [hjpeq]
      exact div_nonneg (by linarith [hA jp (hTpJ jp hjpT)]) (by linarith)
    have htple : ∀ j, (M.G *ᵥ dv) j < 0 → tp * (-(M.G *ᵥ dv) j) ≤
        (M.G *ᵥ ζ) j - M.g0 j - δ := by
      intro j hj
      have h1 : tp ≤ ratp j := Finset.inf'_le _ (by simp [hTp, hj])
      rwa [hratp, le_div_iff₀ (by linarith)] at h1
    have htpeq : tp * (-(M.G *ᵥ dv) jp) = (M.G *ᵥ ζ) jp - M.g0 jp - δ := by
      rw [← htp] at hjpeq
      rw [hjpeq, hratp]
      exact div_mul_cancel₀ _ (by linarith : -(M.G *ᵥ dv) jp ≠ 0)
    set Tm := Finset.univ.filter (fun j => 0 < (M.G *ᵥ dv) j) with hTm
    by_cases hTmne : Tm.Nonempty
    · have hTmJ : ∀ j ∈ Tm, j ∉ J := fun j hj hjJ => by
        simp only [hTm, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [hdJ j hjJ] at hj; exact lt_irrefl _ hj
      set ratm : Fin mt → ℝ := fun j => ((M.G *ᵥ ζ) j - M.g0 j - δ) / ((M.G *ᵥ dv) j)
        with hratm
      set tm := Tm.inf' hTmne ratm with htm
      obtain ⟨jm, hjmT, hjmeq⟩ := Finset.exists_mem_eq_inf' hTmne ratm
      have hjmpos : 0 < (M.G *ᵥ dv) jm := by simpa [hTm] using hjmT
      have htmle : ∀ j, 0 < (M.G *ᵥ dv) j → tm * (M.G *ᵥ dv) j ≤
          (M.G *ᵥ ζ) j - M.g0 j - δ := by
        intro j hj
        have h1 : tm ≤ ratm j := Finset.inf'_le _ (by simp [hTm, hj])
        rwa [hratm, le_div_iff₀ hj] at h1
      have htm0 : 0 ≤ tm := by
        rw [← htm] at hjmeq
        rw [hjmeq]
        exact div_nonneg (by linarith [hA jm (hTmJ jm hjmT)]) hjmpos.le
      have htmeq : tm * (M.G *ᵥ dv) jm = (M.G *ᵥ ζ) jm - M.g0 jm - δ := by
        rw [← htm] at hjmeq
        rw [hjmeq, hratm]
        exact div_mul_cancel₀ _ hjmpos.ne'
      by_cases hlt : tm < tp
      · -- reflect in the backward direction
        refine Bstep (-dv) tm jm htm0 (fun j hj => by
            rw [Matrix.mulVec_neg, Pi.neg_apply, hdJ j hj, neg_zero]) (hTmJ jm hjmT) ?_ ?_ ?_
        · rw [Matrix.mulVec_neg, Pi.neg_apply, neg_neg]; exact htmeq
        · intro j hj
          rw [Matrix.mulVec_neg, Pi.neg_apply, neg_neg]
          rw [Matrix.mulVec_neg, Pi.neg_apply] at hj
          exact htmle j (by linarith)
        · intro j hj
          rw [Matrix.mulVec_neg, Pi.neg_apply] at hj ⊢
          have hj' : (M.G *ᵥ dv) j < 0 := by linarith
          have := htple j hj'
          have : tm * (-(M.G *ᵥ dv) j) ≤ tp * (-(M.G *ᵥ dv) j) :=
            mul_le_mul_of_nonneg_right hlt.le (by linarith)
          linarith
      · push Not at hlt
        refine Bstep dv tp jp htp0 hdJ (hTpJ jp hjpT) htpeq htple ?_
        intro j hj
        have := htmle j hj
        have : tp * (M.G *ᵥ dv) j ≤ tm * (M.G *ᵥ dv) j :=
          mul_le_mul_of_nonneg_right hlt hj.le
        linarith
    · refine Bstep dv tp jp htp0 hdJ (hTpJ jp hjpT) htpeq htple ?_
      intro j hj
      exact absurd ⟨j, by simp [hTm, hj]⟩ hTmne
  obtain ⟨ρ, hρ, hgood⟩ := main _ ∅ rfl
  refine ⟨x, ρ, hρ, C, hCfin, fun ζ hζ => ?_⟩
  obtain ⟨y0, Y, hYC, hrob⟩ := hgood ζ ⟨hζ, by simp⟩
  unfold QC
  exact lt_of_le_of_lt (iInf₂_le (y0, Y) ⟨hYC, hrob⟩) (robCost_affine_lt_top M p ζ ρ _ y0 Y)

/-- **[A6] ⇒ [A4]** -/
theorem A6_to_A4 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : A6 M p → A4 M p := by
  rintro ⟨x, ε, hε, C, -, hC⟩
  refine ⟨x, ε, hε, fun zhat hzhat => ?_⟩
  have h1 := hC zhat hzhat
  unfold QC at h1
  rw [iInf_lt_iff] at h1
  obtain ⟨yY, h1⟩ := h1
  rw [iInf_lt_iff] at h1
  obtain ⟨⟨-, hrob⟩, -⟩ := h1
  exact ⟨fun ζ => yY.1 + yY.2 *ᵥ ζ, ⟨yY.1, yY.2, fun ζ => rfl⟩, hrob⟩

/-- **[A4] ⇒ [A5]** -/
theorem A4_to_A5 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : A4 M p → A5 M p := by
  classical
  rintro ⟨x, ε, hε, hA4⟩
  have hball : ∀ ζ : Fin d → ℝ, ζ ∈ ball p ζ ε := fun ζ => by
    show ‖WithLp.toLp p (ζ - ζ)‖ ≤ ε
    simpa using hε.le
  have hrec : ∀ ζ ∈ Xi M, ∃ y, M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y := by
    intro ζ hζ
    obtain ⟨y, -, hrob⟩ := hA4 ζ hζ
    exact ⟨y ζ, hrob ζ ⟨hball ζ, hζ⟩⟩
  refine ⟨x, ε, hε, fun ζ hζ => ?_, fun F hF => ?_⟩
  · obtain ⟨y, hy⟩ := hrec ζ hζ
    unfold Q
    exact lt_of_le_of_lt (sInf_le ⟨y, hy, rfl⟩) (EReal.coe_lt_top _)
  · have hF' := hF
    obtain ⟨⟨⟨zb, hzb⟩, I, rfl⟩, -⟩ := hF'
    have hzbX : zb ∈ Xi M := hzb.1
    obtain ⟨y, ⟨y0, Y, hyform⟩, hrob⟩ := hA4 zb hzbX
    refine ⟨Y, fun zh hzh => ?_⟩
    have hconst : ∀ kk, (M.G *ᵥ zh) kk = (M.G *ᵥ zb) kk := fun kk =>
      minimalFace_const M hF hzh hzb kk
    -- display (31): a recourse for the shift `H (ẑ - z̄)`
    obtain ⟨yt, hyt⟩ : ∃ yt : Fin r → ℝ, M.H *ᵥ (zh - zb) ≤ M.W *ᵥ yt := by
      by_contra hno
      obtain ⟨l, hl, hWl, hlpos⟩ := farkas_ineq M.W (M.H *ᵥ (zh - zb)) hno
      set β := l ⬝ᵥ (M.H *ᵥ (zh - zb)) with hβ
      set α : ℝ := (|l ⬝ᵥ (M.T *ᵥ x)| + |l ⬝ᵥ M.h zb| + 1) / β with hα
      have hαpos : 0 ≤ α := div_nonneg (by positivity) hlpos.le
      have hpt : zb + α • (zh - zb) ∈ Xi M := by
        intro kk
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [hconst kk, sub_self, mul_zero, add_zero]
        exact hzbX kk
      obtain ⟨ya, hya⟩ := hrec _ hpt
      have hineq : l ⬝ᵥ M.h (zb + α • (zh - zb)) ≤ l ⬝ᵥ (M.T *ᵥ x + M.W *ᵥ ya) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hya j) (hl j)
      have e1 : l ⬝ᵥ (M.T *ᵥ x + M.W *ᵥ ya) = l ⬝ᵥ (M.T *ᵥ x) := by
        rw [dotProduct_add, dotProduct_mulVec l M.W ya, ← mulVec_transpose, hWl,
          zero_dotProduct, add_zero]
      have e2 : l ⬝ᵥ M.h (zb + α • (zh - zb)) = l ⬝ᵥ M.h zb + α * β := by
        simp only [Model.h, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
          dotProduct_smul, smul_eq_mul, hβ]
        ring
      rw [e1, e2] at hineq
      have e3 : α * β = |l ⬝ᵥ (M.T *ᵥ x)| + |l ⬝ᵥ M.h zb| + 1 := by
        rw [hα, div_mul_cancel₀ _ hlpos.ne']
      have := le_abs_self (l ⬝ᵥ (M.T *ᵥ x))
      have := neg_abs_le (l ⬝ᵥ M.h zb)
      linarith
    -- translate the rule from `z̄` to `ẑ`
    have hrule : robFeas M x (ball p zh ε ∩ Xi M)
        (fun ζ => (y0 + yt + Y *ᵥ zb - Y *ᵥ zh) + Y *ᵥ ζ) := by
      intro ζ hζ
      have hζ' : ζ + (zb - zh) ∈ ball p zb ε ∩ Xi M := by
        refine ⟨?_, fun kk => ?_⟩
        · show ‖WithLp.toLp p (ζ + (zb - zh) - zb)‖ ≤ ε
          have : ζ + (zb - zh) - zb = ζ - zh := by abel
          rw [this]; exact hζ.1
        · rw [Matrix.mulVec_add, Matrix.mulVec_sub]
          simp only [Pi.add_apply, Pi.sub_apply]
          rw [hconst kk, sub_self, add_zero]
          exact hζ.2 kk
      have h1 := hrob _ hζ'
      simp only [hyform] at h1
      intro j
      have h1j := h1 j
      have h2j := hyt j
      simp only [Model.h, Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_sub,
        Pi.sub_apply] at h1j h2j ⊢
      linarith
    unfold QC
    exact lt_of_le_of_lt (iInf₂_le (y0 + yt + Y *ᵥ zb - Y *ᵥ zh, Y) ⟨rfl, hrule⟩)
      (robCost_affine_lt_top M p zh ε _ _ Y)

end SROL1Aux

open TwoStageSRO.AsymOpt SROL1Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    List.TFAE [A4 M p, A5 M p, A6 M p] := by
  tfae_have 1 → 2 := A4_to_A5 M p
  tfae_have 2 → 3 := A5_to_A6 M p
  tfae_have 3 → 1 := A6_to_A4 M p
  tfae_finish
