-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.cDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:40.231023+00:00
-- url     : https://prove2.me/submissions/8607b21d-8fe9-4d3c-a7fe-0602d60ad856

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_contDiff_xZx

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
theorem _root_.solution : CDiff := by
  intro n Z a b
  exact ⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩
end PositivityTheory.Rg.Sw.LVs.II
