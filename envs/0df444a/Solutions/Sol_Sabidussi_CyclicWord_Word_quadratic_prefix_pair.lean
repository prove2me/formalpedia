-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.quadratic_prefix_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:56.505643+00:00
-- url     : https://prove2.me/submissions/0d490872-b28f-4a5c-87e9-0ec6553bc4bf

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_transition
import Theorems.Thm_Sabidussi_bracket_add_left
import Theorems.Thm_Sabidussi_bracket_comm
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_quadratic_add
attribute [local simp] Sabidussi.bracket_self



set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))
namespace Sabidussi.CyclicWord.Word
theorem _root_.solution
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    quadratic (W.prefixColor y (W.prev i)) + quadratic (W.prefixColor y i) =
      quadratic (y i) + bracket (y i) (W.prefixColor y (W.prev i)) := by
  let a := W.prefixColor y (W.prev i)
  let b := W.prefixColor y i
  have hab : a + b = y i := W.prefixColor_transition y htotal i
  have hbracket : bracket a b = bracket (y i) a := by
    calc
      bracket a b = bracket b a := bracket_comm _ _
      _ = bracket (a + b) a := by
        rw [bracket_add_left, bracket_self, zero_add]
      _ = bracket (y i) a := by rw [hab]
  calc
    quadratic a + quadratic b =
        (quadratic a + quadratic b + bracket a b) + bracket a b := by
          symm
          calc
            quadratic a + quadratic b + bracket a b + bracket a b =
                (quadratic a + quadratic b) + (bracket a b + bracket a b) := by abel
            _ = quadratic a + quadratic b := by rw [F₂_add_self, add_zero]
    _ = quadratic (a + b) + bracket a b := by rw [quadratic_add]
    _ = quadratic (y i) + bracket (y i) a := by rw [hab, hbracket]
end Sabidussi.CyclicWord.Word
