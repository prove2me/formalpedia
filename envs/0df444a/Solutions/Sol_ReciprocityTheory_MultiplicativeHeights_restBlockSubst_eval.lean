-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.restBlockSubst_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:12.579407+00:00
-- url     : https://prove2.me/submissions/00f48a3a-71fd-4084-a8f2-0e27842f5be6

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
    (fun p => eval (blockPoint y) (lh0Rest (spherePoint x) p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by
  funext ⟨b, j⟩
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [lh0Rest, blockPoint, Fin.insertNthEquiv, Fin.insertNth_zero']
end ReciprocityTheory.MultiplicativeHeights
