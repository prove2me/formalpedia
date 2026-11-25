-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inG_nU_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:15.171825+00:00
-- url     : https://prove2.me/submissions/907f0aa9-79ba-4849-839b-e8d2f8672357

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_herm_isHermitian

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (x : Fin n → Fin n → ℝ) : InG (nU (herm x)) := by
  have hH := herm_isHermitian x
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hH]
end PositivityTheory.Rg.Sw.LVs
