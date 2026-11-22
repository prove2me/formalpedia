-- Prove2me | solution 1 for VectorValuedHolomorphy.existsUnique_hasResidueAt
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:20:17.510745+00:00
-- url     : https://prove2.me/submissions/89af5753-c8b6-47d8-983a-0346f9b63b3d

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic
import Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iff_forall_strongDual

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_existsUnique_hasResidueAt

/-- A continuous linear functional commutes with the complex derivative of a curve in a
topological vector space. -/
theorem hasDerivAt_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {f : ℂ → E} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (ℓ : StrongDual ℂ E) :
    HasDerivAt (fun w => ℓ (f w)) (ℓ (deriv f z)) z := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) z := hf.hasFDerivAt
  have h : HasFDerivAt (fun w => ℓ (f w)) (ℓ.comp (fderiv ℂ f z)) z := by
    refine HasFDerivAt.of_isLittleOTVS ?_
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS
  exact hasFDerivAt_iff_hasDerivAt.mp h

/-- **Division by `z - z₀`.** If `g` is holomorphic near `z₀`, with values in a quasi-complete
Hausdorff locally convex space, then the difference quotient
`z ↦ (z - z₀)⁻¹ • (g z - g z₀)` extends to a function holomorphic near `z₀`. -/
theorem exists_dslope {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {g : ℂ → E} {z₀ : ℂ}
    (hg : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z) :
    ∃ g₁ : ℂ → E, (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g₁ z) ∧
      ∀ z, z ≠ z₀ → g₁ z = (z - z₀)⁻¹ • (g z - g z₀) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  have hgB : DifferentiableOn ℂ g (ball z₀ ε) :=
    fun z hz => (hball z hz).differentiableWithinAt
  let g₁ : ℂ → E := fun z => if z = z₀ then deriv g z₀ else (z - z₀)⁻¹ • (g z - g z₀)
  have hg₁ : DifferentiableOn ℂ g₁ (ball z₀ ε) := by
    rw [VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual isOpen_ball]
    intro ℓ
    have hφ : DifferentiableOn ℂ (fun w => ℓ (g w)) (ball z₀ ε) :=
      (VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual isOpen_ball g).mp hgB ℓ
    have heq : (fun z => ℓ (g₁ z)) = dslope (fun w => ℓ (g w)) z₀ := by
      funext z
      by_cases hz : z = z₀
      · rw [hz, dslope_same]
        simp only [g₁, if_pos rfl]
        exact (hasDerivAt_strongDual_comp (hball z₀ (mem_ball_self hε)) ℓ).deriv.symm
      · rw [dslope_of_ne _ hz, slope_def_field]
        simp only [g₁, if_neg hz, map_smul, map_sub, smul_eq_mul]
        ring
    rw [heq]
    exact (Complex.differentiableOn_dslope (ball_mem_nhds z₀ hε)).mpr hφ
  refine ⟨g₁, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds z₀ hε] with z hz
    exact hg₁.differentiableAt (isOpen_ball.mem_nhds hz)
  · intro z hz
    simp only [g₁, if_neg hz]

/-- **Existence of the principal part.** If `(z - z₀) ^ n • f z` extends holomorphically across
`z₀`, then `f` is, near `z₀`, the sum of a principal part with `n` terms and of a function
holomorphic near `z₀`. Induction on `n`, dividing by `z - z₀` at each step. -/
theorem exists_principal_part {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] (z₀ : ℂ) (n : ℕ) :
    ∀ f g : ℂ → E, (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z) →
      (∀ᶠ z in 𝓝[≠] z₀, g z = (z - z₀) ^ n • f z) →
      ∃ (a : ℕ → E) (h : ℂ → E), (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ h z) ∧
        ∀ᶠ z in 𝓝[≠] z₀,
          f z = (∑ j ∈ Finset.range n, ((z - z₀) ^ (j + 1))⁻¹ • a j) + h z := by
  induction n with
  | zero =>
    intro f g hg hfg
    refine ⟨fun _ => 0, g, hg, ?_⟩
    filter_upwards [hfg] with z hz
    simp [hz]
  | succ n ih =>
    intro f g hg hfg
    obtain ⟨g₁, hg₁, hgg₁⟩ := exists_dslope hg
    have h1 : ∀ᶠ z in 𝓝[≠] z₀,
        g₁ z = (z - z₀) ^ n • (f z - ((z - z₀) ^ (n + 1))⁻¹ • g z₀) := by
      filter_upwards [hfg, eventually_mem_nhdsWithin] with z hz hne
      have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
      rw [hgg₁ z hne, hz, smul_sub, smul_sub, smul_smul, smul_smul]
      congr 2
      · field_simp
        ring
      · field_simp
        ring
    obtain ⟨a, h, hh, hah⟩ := ih _ g₁ hg₁ h1
    refine ⟨Function.update a n (g z₀), h, hh, ?_⟩
    filter_upwards [hah] with z hz
    have hsum : ∑ j ∈ Finset.range n, ((z - z₀) ^ (j + 1))⁻¹ • Function.update a n (g z₀) j
        = ∑ j ∈ Finset.range n, ((z - z₀) ^ (j + 1))⁻¹ • a j :=
      Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_range.mp hj).ne]
    rw [Finset.sum_range_succ, Function.update_self, hsum, add_right_comm, ← hz,
      sub_add_cancel]

/-- **Vanishing of the coefficients of a holomorphic principal part.** In a Hausdorff
topological vector space, if a finite principal part `∑_{j < N} (z - z₀)^{-(j+1)} d_j` agrees
on a punctured neighbourhood of `z₀` with a function continuous at `z₀`, then all its
coefficients vanish. -/
theorem coeff_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] (z₀ : ℂ) (N : ℕ) :
    ∀ (d : ℕ → E) (H : ℂ → E), ContinuousAt H z₀ →
      (∀ᶠ z in 𝓝[≠] z₀, ∑ j ∈ Finset.range N, ((z - z₀) ^ (j + 1))⁻¹ • d j = H z) →
      ∀ j < N, d j = 0 := by
  induction N with
  | zero =>
    intro d H _ _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ N ih =>
    intro d H hH hd
    have hshift : ∀ᶠ z in 𝓝[≠] z₀,
        ∑ j ∈ Finset.range N, ((z - z₀) ^ (j + 1))⁻¹ • d (j + 1) = (z - z₀) • H z - d 0 := by
      filter_upwards [hd, eventually_mem_nhdsWithin] with z hz hne
      have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
      rw [← hz, Finset.sum_range_succ', smul_add, Finset.smul_sum]
      have h1 : (z - z₀) • ((z - z₀) ^ (0 + 1))⁻¹ • d 0 = d 0 := by
        rw [zero_add, pow_one, smul_inv_smul₀ hne']
      rw [h1, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      field_simp
      ring
    have hH' : ContinuousAt (fun z => (z - z₀) • H z - d 0) z₀ :=
      ((continuousAt_id.sub continuousAt_const).smul hH).sub continuousAt_const
    have htail := ih (fun j => d (j + 1)) _ hH' hshift
    have h0 : d 0 = 0 := by
      have hev : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • H z = d 0 := by
        filter_upwards [hd, eventually_mem_nhdsWithin] with z hz hne
        have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
        rw [← hz, Finset.sum_range_succ', Finset.sum_eq_zero (fun j hj => by
          rw [htail j (Finset.mem_range.mp hj), smul_zero]), zero_add, zero_add, pow_one,
          smul_inv_smul₀ hne']
      have ht : Tendsto (fun z => (z - z₀) • H z) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) • H z₀)) :=
        (((continuousAt_id.sub continuousAt_const).smul hH).tendsto).mono_left
          nhdsWithin_le_nhds
      have ht' : Tendsto (fun z => (z - z₀) • H z) (𝓝[≠] z₀) (𝓝 (d 0)) :=
        tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
      have hlim := tendsto_nhds_unique ht' ht
      rw [hlim, sub_self, zero_smul]
    intro j hj
    rcases j with _ | j
    · exact h0
    · exact htail j (Nat.lt_of_succ_lt_succ hj)

/-- **Uniqueness of the residue** (valid in any Hausdorff topological vector space). -/
theorem hasResidueAt_unique {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] {f : ℂ → E} {z₀ : ℂ}
    {r₁ r₂ : E} (h₁ : VectorValuedHolomorphy.HasResidueAt f z₀ r₁)
    (h₂ : VectorValuedHolomorphy.HasResidueAt f z₀ r₂) : r₁ = r₂ := by
  obtain ⟨n₁, a₁, k₁, rfl, hk₁, he₁⟩ := h₁
  obtain ⟨n₂, a₂, k₂, rfl, hk₂, he₂⟩ := h₂
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max n₁ n₂ + 1 := ⟨_, rfl⟩
  have hM₁ : n₁ + 1 ≤ M := by rw [hM]; exact Nat.succ_le_succ (le_max_left _ _)
  have hM₂ : n₂ + 1 ≤ M := by rw [hM]; exact Nat.succ_le_succ (le_max_right _ _)
  -- padding a principal part with zero coefficients
  have pad : ∀ (n : ℕ) (a : ℕ → E) (z : ℂ), n + 1 ≤ M →
      ∑ j ∈ Finset.range (n + 1), ((z - z₀) ^ (j + 1))⁻¹ • a j
        = ∑ j ∈ Finset.range M, ((z - z₀) ^ (j + 1))⁻¹ • (if j ≤ n then a j else 0) := by
    intro n a z hn
    rw [← Finset.sum_subset (Finset.range_mono hn)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    · intro j _ hj
      rw [if_neg (fun hle => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))), smul_zero]
  have key := coeff_eq_zero z₀ M
    (fun j => (if j ≤ n₁ then a₁ j else 0) - (if j ≤ n₂ then a₂ j else 0))
    (fun z => k₂ z - k₁ z)
    (hk₂.self_of_nhds.continuousAt.sub hk₁.self_of_nhds.continuousAt) ?_ 0
    (lt_of_lt_of_le (Nat.succ_pos n₁) hM₁)
  · simpa [sub_eq_zero] using key
  · filter_upwards [he₁, he₂] with z hz₁ hz₂
    rw [pad n₁ a₁ z hM₁] at hz₁
    rw [pad n₂ a₂ z hM₂] at hz₂
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_sub_iff_add_eq_add, ← hz₁, hz₂, add_comm]

end Sol_VectorValuedHolomorphy_existsUnique_hasResidueAt

open VectorValuedHolomorphy in
open Sol_VectorValuedHolomorphy_existsUnique_hasResidueAt in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {f : ℂ → E} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    ∃! r : E, HasResidueAt f z₀ r := by
  obtain ⟨n, g, hg, hfg⟩ := hf
  obtain ⟨a, h, hh, hah⟩ := exists_principal_part z₀ n f g hg hfg
  have hex : HasResidueAt f z₀ ((fun j => if j < n then a j else 0) 0) := by
    refine ⟨n, fun j => if j < n then a j else 0, h, rfl, hh, ?_⟩
    filter_upwards [hah] with z hz
    rw [hz, Finset.sum_range_succ, if_neg (lt_irrefl n), smul_zero, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
  exact ⟨_, hex, fun r' hr' => hasResidueAt_unique hr' hex⟩
