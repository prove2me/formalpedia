-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.imK_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:55.373073+00:00
-- url     : https://prove2.me/submissions/0f04971f-f14c-4811-90d6-bab874443b58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft

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
theorem _root_.solution (e : M2 n) : (imK e)ᴴ = -imK e := by
  ext i j
  simp only [imK, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.LVs.II
