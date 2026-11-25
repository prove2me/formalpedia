-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:13.195034+00:00
-- url     : https://prove2.me/submissions/b77c12bd-3971-4544-916e-884e1e255616

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_reindex_thm

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
theorem _root_.solution : Reindex := CEq.reindex_thm
end PositivityTheory.Rg.Sw.LVs
