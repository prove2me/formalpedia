-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.xZx_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:48:04.052061+00:00
-- url     : https://prove2.me/submissions/1c9aa03e-276c-4689-bd22-8922a1001ead

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
theorem _root_.solution (x Z : M2 n) (i j : Fin n ⊕ Fin n) :
    (x * Z * xᴴ) i j = ∑ l, (∑ m, x i m * Z m l) * starRingEnd ℂ (x j l) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
end PositivityTheory.Rg.Sw.LVs.II
