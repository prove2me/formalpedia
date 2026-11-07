-- Prove2me | solution 1 for QEC.Coding.Why24BooleanANF.evaluate_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:22.137955+00:00
-- url     : https://prove2.me/submissions/6d714093-3c58-409c-9cb4-8c082f105817

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24BooleanANF
open scoped BigOperators
namespace QEC.Coding.Why24BooleanANF
theorem _root_.solution {n : Nat} (word : Fin n → ZMod 2) (coordinate : Fin n) :
    evaluate word (generator coordinate) = word coordinate := by
  rw [evaluate, generator, MonoidAlgebra.lift_single, one_smul]
  change (∏ i ∈ ({coordinate} : Finset (Fin n)), word i) = word coordinate
  exact Finset.prod_singleton _ _
end QEC.Coding.Why24BooleanANF
