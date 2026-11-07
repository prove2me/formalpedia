-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.sum_lowWeightSupport_pow_card_le_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:08:21.772185+00:00
-- url     : https://prove2.me/submissions/1a419d7c-3419-4eae-8df5-1d45493dc859

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r : Nat) (t : ENNReal) :
    (∑ A : LowWeightSupport r, t ^ A.1.card) ≤
      ∑ A : NonemptyVariableSupport r, t ^ A.1.card := by
  let predicate : NonemptyVariableSupport r → Prop :=
    fun A => 5 * A.1.card < 4 * r
  let summand : NonemptyVariableSupport r → ENNReal :=
    fun A => t ^ A.1.card
  have heq :
      (∑ A : LowWeightSupport r, t ^ A.1.card) =
        ∑ A : {A : NonemptyVariableSupport r // predicate A},
          summand A.1 := by
    exact Fintype.sum_equiv
      (lowWeightSupportEquivSubtypeNonempty r)
      (fun A : LowWeightSupport r => t ^ A.1.card)
      (fun A : {A : NonemptyVariableSupport r // predicate A} =>
        summand A.1)
      (fun _ => rfl)
  rw [heq]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype predicate summand
  rw [← hsplit]
  exact le_add_right le_rfl
end QEC.Coding.FiberBundle.RandomBase
