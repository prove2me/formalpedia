-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_nsq_031169476c2f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:46.911027+00:00
-- url     : https://prove2.me/submissions/f8f65534-c22a-46e4-9eea-24773a4b61bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_bil_apply_07404f460fd9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
theorem _root_.solution (z : J → ℂ) : HasFDerivAt nsq ((2 : ℝ) • bil z) z := by
  have h : ∀ p : J, HasFDerivAt (fun z : J → ℂ ↦ reP p z ^ 2 + imaginary p z ^ 2)
      ((2 * reP p z) • reP p + (2 * imaginary p z) • imaginary p) z := by
    intro p
    have h1 := (reP p).hasFDerivAt (x := z) |>.pow 2
    have h2 := (imaginary p).hasFDerivAt (x := z) |>.pow 2
    refine (h1.add h2).congr_fderiv ?_
    ext v
    simp
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ ↦ h p)
  refine hs.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, bil_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
