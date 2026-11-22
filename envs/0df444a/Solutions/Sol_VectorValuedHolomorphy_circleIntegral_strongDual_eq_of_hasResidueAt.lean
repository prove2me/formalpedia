-- Prove2me | solution 1 for VectorValuedHolomorphy.circleIntegral_strongDual_eq_of_hasResidueAt
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:20:23.048803+00:00
-- url     : https://prove2.me/submissions/04bceb0a-3c16-43e1-88df-fac684356398

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_of_hasResidueAt

/-- A continuous linear functional composed with a function that is complex differentiable at a
point (with values in a topological vector space) is complex differentiable at that point. -/
theorem differentiableAt_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {f : ℂ → E} {z : ℂ} (hf : DifferentiableAt ℂ f z) (ℓ : StrongDual ℂ E) :
    DifferentiableAt ℂ (fun w => ℓ (f w)) z := by
  obtain ⟨f', hf'⟩ := hf
  refine ⟨ℓ.comp f', HasFDerivAt.of_isLittleOTVS ?_⟩
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS

/-- A continuous linear functional composed with a holomorphic vector-valued function is
holomorphic. -/
theorem differentiableOn_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {U : Set ℂ} {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (ℓ : StrongDual ℂ E) :
    DifferentiableOn ℂ (fun z => ℓ (f z)) U := by
  intro z hz
  obtain ⟨f', hf'⟩ := hf z hz
  refine ⟨ℓ.comp f', HasFDerivWithinAt.of_isLittleOTVS ?_⟩
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS

/-- The circle integral of a finite principal part `∑ⱼ bⱼ (z - z₀)^{-(j+1)}` around a circle
enclosing `z₀` is `2πi b₀`. -/
theorem circleIntegral_principalPart {z₀ c : ℂ} {ρ : ℝ} (hz₀ : z₀ ∈ ball c ρ) (n : ℕ)
    (b : ℕ → ℂ) :
    (∮ z in C(c, ρ), ∑ j ∈ Finset.range (n + 1), ((z - z₀) ^ (j + 1))⁻¹ * b j)
      = 2 * π * Complex.I * b 0 := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt hz₀
  have hns : z₀ ∉ sphere c |ρ| := by
    rw [abs_of_pos hρ]
    intro h
    exact absurd (mem_ball.mp hz₀) (by rw [mem_sphere.mp h]; exact lt_irrefl _)
  have hrw : ∀ (j : ℕ) (z : ℂ),
      ((z - z₀) ^ (j + 1))⁻¹ * b j = b j * (z - z₀) ^ (-((j : ℤ) + 1)) := by
    intro j z
    rw [zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast, mul_comm]
  have hint : ∀ j : ℕ, CircleIntegrable (fun z => (z - z₀) ^ (-((j : ℤ) + 1))) c ρ := fun j =>
    circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hns))
  simp only [hrw]
  have hint' : ∀ j : ℕ, CircleIntegrable (fun z => b j * (z - z₀) ^ (-((j : ℤ) + 1))) c ρ :=
    fun j => (hint j).const_smul (a := b j)
  rw [circleIntegral.integral_fun_sum (fun j _ => hint' j)]
  simp only [circleIntegral.integral_const_mul]
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · have h0 : (fun z : ℂ => (z - z₀) ^ (-(((0 : ℕ) : ℤ) + 1))) = fun z => (z - z₀)⁻¹ := by
      funext z
      simp
    rw [h0, circleIntegral.integral_sub_inv_of_mem_ball hz₀, mul_comm]
  · intro j _
    rw [circleIntegral.integral_sub_zpow_of_ne (by push_cast; omega), mul_zero]

/-- The scalar residue formula for a function with one pole inside a circle. -/
theorem circleIntegral_eq_of_principalPart {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    {z₀ c : ℂ} {ρ : ℝ} (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ)
    (hg : DifferentiableOn ℂ g (U \ {z₀})) (n : ℕ) (b : ℕ → ℂ) {k : ℂ → ℂ}
    (hk : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ k z)
    (hgk : ∀ᶠ z in 𝓝[≠] z₀,
      g z = (∑ j ∈ Finset.range (n + 1), ((z - z₀) ^ (j + 1))⁻¹ * b j) + k z) :
    (∮ z in C(c, ρ), g z) = 2 * π * Complex.I * b 0 := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt hz₀
  have hsph : ∀ z ∈ sphere c ρ, z ≠ z₀ := by
    intro z hz h
    rw [h] at hz
    exact absurd (mem_ball.mp hz₀) (by rw [mem_sphere.mp hz]; exact lt_irrefl _)
  set P : ℂ → ℂ := fun z => ∑ j ∈ Finset.range (n + 1), ((z - z₀) ^ (j + 1))⁻¹ * b j with hP
  -- the principal part is holomorphic off `z₀`
  have hPd : ∀ z, z ≠ z₀ → DifferentiableAt ℂ P z := by
    intro z hz
    have hz' : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.mul_const ?_ _
    exact ((differentiableAt_id.sub_const z₀).pow (j + 1)).inv (pow_ne_zero _ hz')
  -- `g` is holomorphic at every point of `U` other than `z₀`
  have hgd : ∀ z ∈ U, z ≠ z₀ → DifferentiableAt ℂ g z := by
    intro z hzU hz
    exact (hg z ⟨hzU, hz⟩).differentiableAt
      ((hU.sdiff isClosed_singleton).mem_nhds ⟨hzU, hz⟩)
  -- the regular part, extended across `z₀`
  set G : ℂ → ℂ := Function.update (fun z => g z - P z) z₀ (k z₀) with hG
  have hGd : ∀ z ∈ closedBall c ρ, DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hzz : z = z₀
    · subst hzz
      have hev : G =ᶠ[𝓝 z] k := by
        have h1 : ∀ᶠ w in 𝓝 z, w ≠ z → g w = P w + k w := by
          have := hgk
          rw [eventually_nhdsWithin_iff] at this
          exact this
        filter_upwards [h1] with w hw
        by_cases hwz : w = z
        · rw [hwz, hG, Function.update_self]
        · rw [hG, Function.update_of_ne hwz]
          show g w - P w = k w
          rw [hw hwz]
          ring
      exact hk.self_of_nhds.congr_of_eventuallyEq hev
    · have hev : G =ᶠ[𝓝 z] fun w => g w - P w := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hzz] with w hw
        rw [hG, Function.update_of_ne hw]
      exact ((hgd z (hcρ hz) hzz).sub (hPd z hzz)).congr_of_eventuallyEq hev
  have hGc : ContinuousOn G (closedBall c ρ) := fun z hz =>
    (hGd z hz).continuousAt.continuousWithinAt
  have hzero : (∮ z in C(c, ρ), G z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
      Set.countable_empty hGc (fun z hz => hGd z (ball_subset_closedBall hz.1))
  -- on the circle `G = g - P`
  have hcongr : (∮ z in C(c, ρ), G z) = ∮ z in C(c, ρ), (g z - P z) := by
    refine circleIntegral.integral_congr hρ.le fun z hz => ?_
    show G z = g z - P z
    rw [hG, Function.update_of_ne (hsph z hz)]
  have hgi : CircleIntegrable g c ρ := by
    refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
    exact (hgd z (hcρ (sphere_subset_closedBall hz)) (hsph z hz)).continuousAt.continuousWithinAt
  have hPi : CircleIntegrable P c ρ := by
    refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
    exact (hPd z (hsph z hz)).continuousAt.continuousWithinAt
  rw [hcongr, circleIntegral.integral_sub hgi hPi, sub_eq_zero] at hzero
  rw [hzero]
  exact circleIntegral_principalPart hz₀ n b

end Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_of_hasResidueAt

open VectorValuedHolomorphy
open Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_of_hasResidueAt

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    {z₀ c : ℂ} {ρ : ℝ} (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ)
    (hf : DifferentiableOn ℂ f (U \ {z₀})) {r : E} (hr : HasResidueAt f z₀ r)
    (ℓ : StrongDual ℂ E) :
    (∮ z in C(c, ρ), ℓ (f z)) = 2 * π * Complex.I * ℓ r := by
  obtain ⟨n, a, h, ha0, hh, hfe⟩ := hr
  rw [← ha0]
  refine circleIntegral_eq_of_principalPart hU hcρ hz₀ (differentiableOn_strongDual_comp hf ℓ) n
    (fun j => ℓ (a j)) (k := fun z => ℓ (h z)) ?_ ?_
  · filter_upwards [hh] with z hz
    exact differentiableAt_strongDual_comp hz ℓ
  · filter_upwards [hfe] with z hz
    rw [hz, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
