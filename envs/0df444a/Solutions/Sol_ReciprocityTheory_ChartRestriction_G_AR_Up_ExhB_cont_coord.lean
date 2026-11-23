-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.cont_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:47.7448+00:00
-- url     : https://prove2.me/submissions/e7909b06-56fe-4440-929c-50dd71a15f47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
theorem _root_.solution {n : ℕ} (i : Fin n) : Continuous fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.continuous _
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
