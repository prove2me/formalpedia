-- Prove2me | solution 1 for TreeStack.stack_eq_estim_of_two_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:58:07.83853+00:00
-- url     : https://prove2.me/submissions/614ef209-16e4-487b-bb42-953e49129046

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_stack_eq_estim

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T := by
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact stack_eq_estim T
end TreeStack
