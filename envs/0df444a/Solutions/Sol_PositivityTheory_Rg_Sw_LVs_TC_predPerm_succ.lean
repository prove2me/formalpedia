-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.predPerm_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:51.568032+00:00
-- url     : https://prove2.me/submissions/03c47039-712c-4950-8019-233f17585327

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (i : Fin k) :
    (predPerm σ h0 i).succ = σ i.succ := by
  simp [predPerm]
end PositivityTheory.Rg.Sw.LVs.TC
