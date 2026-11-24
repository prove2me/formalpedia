-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.comm_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:48.278505+00:00
-- url     : https://prove2.me/submissions/f8652e67-661b-413b-bbbd-88b963ddb6da

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_JJ_conjTranspose

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution {e : M2 n} (he : e * JJ n = JJ n * e) : eᴴ * JJ n = JJ n * eᴴ := by
  have h := congrArg conjTranspose he
  rw [conjTranspose_mul, conjTranspose_mul, JJ_conjTranspose] at h
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] at h
  exact h.symm
end PositivityTheory.Rg.Sw.LVs.II
