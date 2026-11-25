-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegRadialWeight_hasCompactSupport_radial_9dbe1033b1d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:47.145799+00:00
-- url     : https://prove2.me/submissions/ccadb572-3d9b-48a3-9ee9-1cedcf995050

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegRadialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegRadialWeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RegRadialWeight
theorem _root_.solution (x : Fin n → ℂ) (F : ℝ → ℝ) (R : ℝ) (hF : ∀ t, R ≤ t → F t = 0) :
    HasCompactSupport (fun z : Fin n → ℂ => F (euclPot (z - x))) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt |R|)) fun z hz => ?_
  by_contra hne
  apply hz
  have hlt : euclPot (z - x) < R := by
    by_contra h
    exact hne (hF _ (not_lt.mp h))
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  have hj : ‖(z - x) j‖ ^ 2 ≤ euclPot (z - x) :=
    Finset.single_le_sum (f := fun j => ‖(z - x) j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  calc ‖(z - x) j‖ = Real.sqrt (‖(z - x) j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt |R| := Real.sqrt_le_sqrt (by linarith [le_abs_self R])
end GroundTheory.Heights₂.Heights.RegRadialWeight
