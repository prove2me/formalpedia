-- Prove2me | solution 1 for Stanley.eval_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:20.85662+00:00
-- url     : https://prove2.me/submissions/5ecc3bbd-be0d-4d9f-8bfe-54195721ad28

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_chromaticPolynomial_eq_external
public import Theorems.Thm_SimpleGraph_ChromaticPolynomial_eval


set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution (α : Type v) [Fintype α] :
    (chromaticPolynomial G).eval (Fintype.card α : ℤ) = Fintype.card (G.Coloring α) :=
  by rw [chromaticPolynomial_eq_external]; exact G.ChromaticPolynomial_eval ℤ α
end Stanley
