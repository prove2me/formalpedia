-- Prove2me | solution 1 for QEC.Coding.Why24BooleanANF.generator_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:04.91808+00:00
-- url     : https://prove2.me/submissions/a95c9337-7c2b-4433-a145-e7b0c7504895

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24BooleanANF
open scoped BigOperators
namespace QEC.Coding.Why24BooleanANF
theorem _root_.solution {n : Nat} (coordinate : Fin n) :
    generator coordinate * generator coordinate = generator coordinate := by
  have hmonomial :
      (⟨{coordinate}⟩ : Monomial n) * ⟨{coordinate}⟩ = ⟨{coordinate}⟩ := by
    apply Monomial.ext
    simp only [mul_support]
    exact Finset.union_self {coordinate}
  rw [generator, MonoidAlgebra.single_mul_single, hmonomial, one_mul]
end QEC.Coding.Why24BooleanANF
