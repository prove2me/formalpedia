-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.equivar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:37.415804+00:00
-- url     : https://prove2.me/submissions/28d4f1e6-7fd8-4afb-8656-7678a26b42e6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_equivar_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Equivar := CEq.equivar_thm
end PositivityTheory.Rg.Sw.LVs
