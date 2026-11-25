-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:57.201554+00:00
-- url     : https://prove2.me/submissions/939d83b6-5f50-4c05-a3f4-149d211f6f96

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
theorem _root_.solution (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := rfl
end PositivityTheory.Rg.Sw.LVs.II
