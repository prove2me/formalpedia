-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:51.508498+00:00
-- url     : https://prove2.me/submissions/c668b1e2-acee-42ae-8c03-5430df495cc2

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
theorem _root_.solution (M : M2 n) : M = fromBlocks (M.toBlocks₁₁ - M.toBlocks₂₂) (M.toBlocks₁₂ + M.toBlocks₂₁) 0 0 +
    ∑ a, ∑ b, (M.toBlocks₂₂ a b • eA a b + (-M.toBlocks₂₁ a b) • eB a b) := by
  ext i j
  rcases i with a' | a' <;> rcases j with b' | b' <;>
    simp [eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
end PositivityTheory.Rg.Sw.LVs.II
