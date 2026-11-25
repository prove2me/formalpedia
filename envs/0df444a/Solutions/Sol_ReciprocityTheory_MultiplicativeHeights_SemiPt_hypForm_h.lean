-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.hypForm_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:26.13142+00:00
-- url     : https://prove2.me/submissions/7f768c7d-2d20-479a-bb38-c6f5f6c83ccb

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by
  rw [HermForm.h]
  have e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b =
      (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0) := by
    intro a
    simp only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases ha : a = j <;> simp [ha]
    · by_cases ha : a = p <;> simp [ha]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp [Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
