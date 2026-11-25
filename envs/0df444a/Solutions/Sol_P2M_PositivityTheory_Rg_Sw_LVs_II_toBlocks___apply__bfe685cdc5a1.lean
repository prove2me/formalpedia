-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:56.845334+00:00
-- url     : https://prove2.me/submissions/dd947d53-3a21-4ce1-9d3c-79aef131c087

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := rfl
end PositivityTheory.Rg.Sw.LVs.II
