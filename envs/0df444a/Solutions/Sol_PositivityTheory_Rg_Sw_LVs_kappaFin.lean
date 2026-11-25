-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.kappaFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:52.073537+00:00
-- url     : https://prove2.me/submissions/a7e10491-333a-4c69-8359-55f565f1562d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_capelli_determinant_integer_rising

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : KappaFin := fun N t => CK.capelli_determinant_integer_rising t N
end PositivityTheory.Rg.Sw.LVs
