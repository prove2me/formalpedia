-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_lift_854fe137c8a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:17.03605+00:00
-- url     : https://prove2.me/submissions/1a4370cd-9cc5-4b2f-ae3a-4115e07c6bf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (R : Res ι P e) (x : R.R.M) (j : Fin R.atlas.n) :
    ContDiffOn ℝ ∞ (fun y => R.liftAt x ((R.atlas.chart j).symm y))
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :=
  contDiffOn_pi.mpr fun q => ((res_holo R x q j).contDiffOn_of_completeSpace).restrict_scalars ℝ
end GroundTheory.Heights₂.Heights.Inter
