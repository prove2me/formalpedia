-- Prove2me | solution 1 for Stanley.chromaticPolynomial_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:54.816611+00:00
-- url     : https://prove2.me/submissions/f80baa62-30da-4f6b-ba0b-af5620bf86ba

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
public import Theorems.Thm_Stanley_orientationCount_induce_univ
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_eval_card
public import Theorems.Thm_Stanley_polynomial_ext_nat
attribute [local simp] Stanley.chromaticPolynomial_induce_univ


attribute [local simp] Stanley.orientationCount_induce_univ

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution [IsEmpty V] : chromaticPolynomial G = 1 := by
  apply polynomial_ext_nat
  intro n
  let c : G.Coloring (Fin n) := Coloring.mk (fun v => isEmptyElim v)
    (fun {v} => isEmptyElim v)
  let : Unique (G.Coloring (Fin n)) :=
    { default := c, uniq := fun _ => Subsingleton.elim _ _ }
  simpa using eval_card G (Fin n)
end Stanley
