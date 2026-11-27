-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_sup_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:27:38.017247+00:00
-- url     : https://prove2.me/submissions/0d8198ee-be9c-489c-85b8-2c5fd6954944

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupLeL2NormSections
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_smul_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_smul_mem_pts_coord
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous n) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ n := by
  classical
  have hρc : ContinuousOn m.ρ {z | z ≠ 0} := hg.semipos.1.continuousOn
  set K : Set (Ix κ → ℂ) := Metric.sphere 0 1 ∩
    {z | ∀ g ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) g) = 0} with hKdef
  have hcl : IsClosed {z : Ix κ → ℂ | ∀ g ∈ coordIdeal ℤ x,
      eval z (map (Int.castRingHom ℂ) g) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval _) continuous_const
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right hcl
  have hsub : K ⊆ {z | z ≠ 0} := fun z hz h0 => by
    have := hz.1
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
    exact zero_ne_one this
  have hF : ContinuousOn (fun z => ‖eval z f‖ / m.ρ z ^ n) K :=
    (continuous_eval f).norm.continuousOn.div ((hρc.mono hsub).pow n)
      fun z hz => pow_ne_zero n (m.pos z (hsub hz)).ne'
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF
  refine ⟨C, fun z hz => ?_⟩
  have ht : 0 < ‖z‖ := norm_pos_iff.mpr hz.1
  set c : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖z‖⁻¹ := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcn
    exact (inv_pos.mpr ht).ne' hcn.symm
  have hzK : c • z ∈ K := by
    refine ⟨?_, (smul_mem_pts_coord x hz hc0).2⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ ht.ne']
  have h1 := hC _ hzK
  have hρ : 0 < m.ρ z := m.pos z hz.1
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  rw [eval_smul_of_isHomogeneous hf, m.smul, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero n hcpos.ne'), Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg hρ.le n))] at h1
  exact (div_le_iff₀ (pow_pos hρ n)).mp h1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
