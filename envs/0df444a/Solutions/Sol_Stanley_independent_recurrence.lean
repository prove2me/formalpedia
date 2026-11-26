-- Prove2me | solution 1 for Stanley.independent_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:42.192326+00:00
-- url     : https://prove2.me/submissions/fe4b5cbe-5206-46d5-ae11-578c5372b10d

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_convolution
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_eval_zero
public import Theorems.Thm_Stanley_eval_one_induce
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
theorem _root_.solution [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (-1) else 0) = 0 := by
  have h := convolution G 1 (-1)
  simpa only [add_neg_cancel, eval_zero, eval_one_induce, ite_mul, one_mul, zero_mul] using h.symm
end Stanley
