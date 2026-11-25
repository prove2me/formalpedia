-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:03.468361+00:00
-- url     : https://prove2.me/submissions/db83ea9c-5ddb-4392-a3c5-c1348c6316b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (F : (Fin g → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFc : Continuous F)
    (hs : ∀ u, Summable fun k : Fin g → ℤ => F (intVec k + u)) :
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ∑' k : Fin g → ℤ, F (intVec k + u) = ∫ x, F x := by
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup :=
    (latticeEquiv (g := g)).symm.injective.countable
  have hD := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin g)) (volume : Measure (Fin g → ℝ))
  have hDI : ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g)) =ᵐ[volume]
      Set.Icc (0 : Fin g → ℝ) 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, ← Set.pi_univ_Icc]
    exact Measure.ae_eq_set_pi (fun i _ => Ico_ae_eq_Icc)
  have hP : ∀ u, ∑' k, F (intVec k + u) = (∑' k, ENNReal.ofReal (F (intVec k + u))).toReal := by
    intro u
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u),
      ENNReal.toReal_ofReal (tsum_nonneg fun k => hF0 _)]
  have hPm : Measurable fun u => ∑' k : Fin g → ℤ, F (intVec k + u) := by
    simp_rw [hP]
    exact (Measurable.tsum fun k => ENNReal.measurable_ofReal.comp
      (hFc.measurable.comp (measurable_const_add _))).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => tsum_nonneg fun k => hF0 _)
      hPm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFc.aestronglyMeasurable]
  congr 1
  rw [hD.lintegral_eq_tsum'' (fun x => ENNReal.ofReal (F x)), ← setLIntegral_congr hDI,
    ← lintegral_tsum (μ := volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g))))
      (f := fun (γ : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup)
        (x : Fin g → ℝ) => ENNReal.ofReal (F (γ +ᵥ x)))
      (fun γ => (ENNReal.measurable_ofReal.comp
        (hFc.measurable.comp (measurable_const_vadd γ))).aemeasurable)]
  refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun u _ => ?_)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u)]
  rw [← (latticeEquiv (g := g)).tsum_eq]
  rfl
end GroundTheory.Heights₂.Heights.KTheta
