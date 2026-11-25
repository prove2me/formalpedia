-- Prove2me | solution 1 for PlankProblem.davenport_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:11.125093+00:00
-- url     : https://prove2.me/submissions/0f551af8-a24a-4d0c-b315-9d0c427d0005

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
public import Theorems.Thm_PlankProblem_core_theorem
public import Theorems.Thm_PlankProblem_sum_smul_mem_of_abs_sum_le
public import Theorems.Thm_PlankProblem_ne_of_mem_interior_of_subset_halfspace

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (f : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hf : ∀ i, f i ≠ 0)
    (c : Fin n → ℝ) :
    ∃ t : Rn,
      homothet t (1 / (n + 1 : ℝ)) K ⊆ K ∧
      ∀ i x,
        x ∈ interior (homothet t (1 / (n + 1 : ℝ)) K) →
        f i x ≠ c i := by
  classical
  obtain ⟨c0, hc0⟩ := hsymm
  obtain ⟨hKc, hKconv, p, hp⟩ := hK
  -- the body centred at the origin
  set K0 : Set Rn := {x | c0 + x ∈ K} with hK0
  have hK0conv : Convex ℝ K0 := by
    intro a ha b hb α β hα hβ hab
    have := hKconv ha hb hα hβ hab
    show c0 + (α • a + β • b) ∈ K
    convert this using 1
    calc c0 + (α • a + β • b) = (α + β) • c0 + (α • a + β • b) := by rw [hab, one_smul]
      _ = α • (c0 + a) + β • (c0 + b) := by module
  have hK0neg : ∀ x ∈ K0, -x ∈ K0 := by
    intro x hx
    have := (hc0 _).mp hx
    show c0 + -x ∈ K
    convert this using 1
    module
  have hpK : p ∈ K := interior_subset hp
  have hq : p - c0 ∈ K0 := by show c0 + (p - c0) ∈ K; simpa using hpK
  have hK00 : (0 : Rn) ∈ K0 := by
    have := hK0conv hq (hK0neg _ hq) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hK0c : IsCompact K0 := (Homeomorph.addLeft c0).isCompact_preimage.mpr hKc
  -- support points
  have hsupp : ∀ i, ∃ v ∈ K0, 0 < f i v ∧ ∀ k ∈ K0, |f i k| ≤ f i v := by
    intro i
    obtain ⟨v, hv, hmax⟩ := hK0c.exists_isMaxOn ⟨0, hK00⟩
      (LinearMap.continuous_of_finiteDimensional (f i)).continuousOn
    have habs : ∀ k ∈ K0, |f i k| ≤ f i v := by
      intro k hk
      have h1 : f i k ≤ f i v := hmax hk
      have h2 : f i (-k) ≤ f i v := hmax (hK0neg k hk)
      rw [map_neg] at h2
      exact abs_le.mpr ⟨by linarith, h1⟩
    refine ⟨v, hv, ?_, habs⟩
    obtain ⟨u, hu⟩ : ∃ u, f i u ≠ 0 := by
      by_contra h
      push Not at h
      exact hf i (LinearMap.ext h)
    have ht : Filter.Tendsto (fun t : ℝ => p + t • u) (nhds 0) (nhds p) := by
      have : Continuous (fun t : ℝ => p + t • u) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, p + t • u ∈ K :=
      (ht.eventually (mem_interior_iff_mem_nhds.mp hp)).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, htK, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    have hq' : p + t • u - c0 ∈ K0 := by show c0 + (p + t • u - c0) ∈ K; simpa using htK
    have hdiff : f i (p + t • u - c0) - f i (p - c0) = t * f i u := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul]; ring
    have hne : f i (p + t • u - c0) ≠ 0 ∨ f i (p - c0) ≠ 0 := by
      by_contra h
      push Not at h
      rw [h.1, h.2] at hdiff
      exact mul_ne_zero ht0' hu (by linarith)
    rcases hne with h | h
    · exact lt_of_lt_of_le (abs_pos.mpr h) (habs _ hq')
    · exact lt_of_lt_of_le (abs_pos.mpr h) (habs _ hq)
  choose v hvK0 hvpos hvmax using hsupp
  -- the linear map sending the standard basis to the support points
  let A : Rn →ₗ[ℝ] Rn := ∑ j, (EuclideanSpace.proj j : Rn →L[ℝ] ℝ).toLinearMap.smulRight (v j)
  have hA : ∀ z, A z = ∑ j, z j • v j := fun z => by simp [A]
  have hAe : ∀ i, A (EuclideanSpace.basisFun (Fin n) ℝ i) = v i := fun i => by
    simp [hA]
  let ℓ : Fin n → (Rn →ₗ[ℝ] ℝ) := fun i => (f i (v i))⁻¹ • ((f i).comp A)
  have hℓ : ∀ i, ℓ i (EuclideanSpace.basisFun (Fin n) ℝ i) = 1 := fun i => by
    simp only [ℓ, LinearMap.smul_apply, LinearMap.comp_apply, hAe, smul_eq_mul]
    exact inv_mul_cancel₀ (hvpos i).ne'
  set r : ℝ := 1 / (n + 1 : ℝ) with hr
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hrpos : 0 < r := by positivity
  have hrn : r * (n + 1) = 1 := by rw [hr]; field_simp
  obtain ⟨z, hz, hzℓ⟩ := core_theorem (EuclideanSpace.basisFun (Fin n) ℝ) ℓ hℓ
    (fun i => (n + 1) * (c i - f i c0) / f i (v i))
  -- `∑ |zⱼ| ≤ n`
  have hzsum : ∑ j, |z j| ≤ n := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |z j|)
    have h2 : ‖z‖ ^ 2 = ∑ j, |z j| ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp
    have h3 : ‖z‖ ^ 2 ≤ n := by
      calc ‖z‖ ^ 2 ≤ (Real.sqrt n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        _ = n := Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    rw [← h2] at h1
    have h4 : (∑ j, |z j|) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h4 (Nat.cast_nonneg n)).2
  -- the centre of the homothet
  refine ⟨c0 + r • A z - r • c0, ?_, ?_⟩
  all_goals
    have hdesc : ∀ x ∈ homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K,
        ∃ k0 ∈ K0, x = c0 + r • (A z + k0) := by
      intro x hx
      obtain ⟨y, ⟨k, hk, rfl⟩, rfl⟩ := hx
      refine ⟨k - c0, by show c0 + (k - c0) ∈ K; simpa using hk, ?_⟩
      simp only [vadd_eq_add]
      module
  · -- the homothet lies in `K`
    intro x hx
    obtain ⟨k0, hk0, rfl⟩ := hdesc x hx
    show c0 + r • (A z + k0) ∈ K
    have hmem := sum_smul_mem_of_abs_sum_le hK0conv hK00 hK0neg
      (Sum.elim v (fun _ : Unit => k0)) (by rintro (j | _) <;> simp [hvK0, hk0])
      (Sum.elim (fun j => r * z j) (fun _ : Unit => r)) (by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
          Finset.sum_singleton, abs_mul, abs_of_pos hrpos]
        rw [← Finset.mul_sum]
        nlinarith)
    have heq : ∑ s, Sum.elim (fun j => r * z j) (fun _ : Unit => r) s •
        Sum.elim v (fun _ : Unit => k0) s = r • (A z + k0) := by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton, hA, smul_add, Finset.smul_sum, mul_smul]
    rw [heq] at hmem
    exact hmem
  · -- the interior of the homothet misses every hyperplane
    intro i x hx
    set g := ℓ i z - (n + 1) * (c i - f i c0) / f i (v i) with hg
    have hgi : 1 ≤ |g| := hzℓ i
    have hval : ∀ k0 ∈ K0,
        f i (c0 + r • (A z + k0)) - c i = r * f i (v i) * g + r * f i k0 := by
      intro k0 _
      have hv0 := (hvpos i).ne'
      have e : f i (v i) * (f i (v i))⁻¹ = 1 := mul_inv_cancel₀ hv0
      simp only [hg, ℓ, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_add,
        map_smul, div_eq_mul_inv]
      linear_combination (-r * f i (A z) + r * (n + 1) * (c i - f i c0)) * e +
        (c i - f i c0) * hrn
    have hfv := hvpos i
    rcases le_abs'.mp hgi with hneg | hpos
    · have hsub : homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K ⊆
          {x | (-c i) ≤ (-f i) x} := by
        intro y hy
        obtain ⟨k0, hk0, rfl⟩ := hdesc y hy
        have h1 := hval k0 hk0
        have h2 := (abs_le.mp (hvmax i k0 hk0)).2
        simp only [mem_ofPred_eq, LinearMap.neg_apply]
        nlinarith [mul_le_mul_of_nonneg_left h2 hrpos.le,
          mul_le_mul_of_nonneg_left hneg (mul_pos hrpos hfv).le]
      have := ne_of_mem_interior_of_subset_halfspace (neg_ne_zero.mpr (hf i)) hsub hx
      intro h
      apply this
      simp [h]
    · have hsub : homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K ⊆
          {x | c i ≤ f i x} := by
        intro y hy
        obtain ⟨k0, hk0, rfl⟩ := hdesc y hy
        have h1 := hval k0 hk0
        have h2 := (abs_le.mp (hvmax i k0 hk0)).1
        simp only [mem_ofPred_eq]
        nlinarith [mul_le_mul_of_nonneg_left h2 hrpos.le,
          mul_le_mul_of_nonneg_left hpos (mul_pos hrpos hfv).le]
      exact ne_of_mem_interior_of_subset_halfspace (hf i) hsub hx
end PlankProblem
