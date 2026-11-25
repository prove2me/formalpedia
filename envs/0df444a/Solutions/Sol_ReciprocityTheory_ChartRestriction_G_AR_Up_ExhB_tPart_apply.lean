-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.tPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:05.271055+00:00
-- url     : https://prove2.me/submissions/93e8c746-9f51-4a74-b0c5-b3df97d45fd5

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
theorem _root_.solution {f p q N' : ℕ} (v : V (nD f p q + N')) (j : Fin N') :
    tPart v j = v (Fin.natAdd (nD f p q) j) := by
  simp [tPart]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
