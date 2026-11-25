-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:01.724056+00:00
-- url     : https://prove2.me/submissions/6b7e1263-3c7c-4792-960d-0338f66a3bce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (R : Res ι P e) (x x' : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (hy' : y ∈ R.R.src (R.idx x')) :
    ReciprocityTheory.AnForm.R.SameOrbit (R.liftAt x y) (R.liftAt x' y) :=
  R.R.compat _ _ y ⟨hy, hy'⟩
end GroundTheory.Heights₂.Heights.Inter
