-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:32.030488+00:00
-- url     : https://prove2.me/submissions/89316835-bfdb-4fa6-9a29-39e533377290

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_nonneg_of_isLocalMin_e6e314957576
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hmin : IsLocalMin f z) (e : J → ℂ) : 0 ≤ fderiv ℝ (fderiv ℝ f) z e e := by
  rw [← deriv_deriv_line hf e]
  have hc : Continuous fun s : ℝ => z + s • e := continuous_const.add (continuous_id.smul continuous_const)
  have hz : z + (0 : ℝ) • e = z := by simp
  refine deriv_deriv_nonneg_of_isLocalMin ?_ ?_
  · have h : IsLocalMin f (z + (0 : ℝ) • e) := by rw [hz]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun s : ℝ => z + s • e) (b := 0) h hc.continuousAt
  · exact ContinuousAt.comp_of_eq hf.continuousAt hc.continuousAt hz
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
