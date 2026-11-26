-- Prove2me | solution 1 for Stanley.eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:05.736433+00:00
-- url     : https://prove2.me/submissions/fafa2ac4-3784-482a-8a27-97716ea78c83

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_eval_card
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution [Nonempty V] : (chromaticPolynomial G).eval 0 = 0 := by
  have : IsEmpty (G.Coloring (Fin 0)) :=
    ⟨fun c => Fin.elim0 (c (Classical.choice (inferInstance : Nonempty V)))⟩
  simpa using eval_card G (Fin 0)
end Stanley
