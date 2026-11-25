-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.eB_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:45.341686+00:00
-- url     : https://prove2.me/submissions/b8c30ed6-742b-4cb4-bc79-2de43881f3a2

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
theorem _root_.solution (M : M2 n) (a b : Fin n) : (eB a b * M) (Sum.inr a) (Sum.inl b) = -M (Sum.inl b) (Sum.inl b) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]
end PositivityTheory.Rg.Sw.LVs.II
