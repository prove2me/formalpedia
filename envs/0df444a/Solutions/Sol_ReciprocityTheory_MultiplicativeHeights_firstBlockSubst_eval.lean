-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:03.552387+00:00
-- url     : https://prove2.me/submissions/e40c55d0-0ac9-4cf8-8962-fa2a57533d05

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
theorem _root_.solution {B n : ℕ} (x : UnitSphereC n) (y : BlockSphere B n) :
    (fun p => eval (spherePoint x) (lh0First y p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by
  funext ⟨b, j⟩
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [lh0First, blockPoint, Fin.insertNthEquiv, Fin.insertNth_zero']
end ReciprocityTheory.MultiplicativeHeights
