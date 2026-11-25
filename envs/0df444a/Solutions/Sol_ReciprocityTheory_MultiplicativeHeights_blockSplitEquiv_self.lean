-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockSplitEquiv_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:51.783918+00:00
-- url     : https://prove2.me/submissions/36a8f46d-3e3b-44ed-b7b2-54304154e5bd

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (u : BlockSphere (B + 1) n) :
    (lh0Split B n).symm (u 0, fun b => u b.succ) = u := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext i
  refine Fin.cases ?_ (fun b => ?_) i <;> simp [Fin.insertNthEquiv, Fin.insertNth_zero']
end ReciprocityTheory.MultiplicativeHeights
