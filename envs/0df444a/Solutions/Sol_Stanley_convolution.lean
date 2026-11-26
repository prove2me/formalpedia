-- Prove2me | solution 1 for Stanley.convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:39.894445+00:00
-- url     : https://prove2.me/submissions/347f0ba7-a28a-410e-a504-e142eb75d9f5

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_polynomial_ext_nat
public import Theorems.Thm_Stanley_eval_add_nat

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution (a b : ℤ) :
    (chromaticPolynomial G).eval (a + b) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval a *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval b := by
  classical
  have step (m : ℕ) :
      (chromaticPolynomial G).comp (X + C (m : ℤ)) =
        ∑ s : Finset V, chromaticPolynomial (G.induce (s : Set V)) *
          C ((chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ)) := by
    apply polynomial_ext_nat
    intro n
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using eval_add_nat G n m
  have step' (a : ℤ) (m : ℕ) :
      (chromaticPolynomial G).eval (a + (m : ℤ)) =
        ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval a *
          (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ) := by
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using congrArg (Polynomial.eval a) (step m)
  have final : (chromaticPolynomial G).comp (C a + X) =
      ∑ s : Finset V, C ((chromaticPolynomial (G.induce (s : Set V))).eval a) *
        chromaticPolynomial (G.induce (s : Set V)ᶜ) := by
    apply polynomial_ext_nat
    intro m
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using step' a m
  simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using congrArg (Polynomial.eval b) final
end Stanley
