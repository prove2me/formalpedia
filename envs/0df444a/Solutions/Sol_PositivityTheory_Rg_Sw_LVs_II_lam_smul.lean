-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.lam_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:59.462825+00:00
-- url     : https://prove2.me/submissions/3de0016e-46d8-44a0-9a95-beb6d98bc800

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (c : ℂ) (Y : M2 n) : lam (c • Y) = c * lam Y := by
  simp only [lam]
  have h1 : (c • Y).toBlocks₁₁ = c • Y.toBlocks₁₁ := by ext; simp [Matrix.toBlocks₁₁]
  have h2 : (c • Y).toBlocks₂₂ = c • Y.toBlocks₂₂ := by ext; simp [Matrix.toBlocks₂₂]
  rw [h1, h2, Matrix.trace_smul, Matrix.trace_smul]; simp only [smul_eq_mul]; ring
end PositivityTheory.Rg.Sw.LVs.II
