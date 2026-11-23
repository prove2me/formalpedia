-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:51.32993+00:00
-- url     : https://prove2.me/submissions/c907c365-dde4-429f-9641-e5adb9c6090d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Theorems.Thm_Bl_DetMonotoneStarMulSelf_goal1
import Theorems.Thm_Bl_PosDefOfRealQuadratic_goal1


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
theorem _root_.solution {X : Type*} [TopologicalSpace X] {m : ℕ}
    (A : X → Matrix (Fin m) (Fin m) ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  first | exact Bl.PosDefOfRealQuadratic.goal1 .. | (apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption) | (intros; apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
