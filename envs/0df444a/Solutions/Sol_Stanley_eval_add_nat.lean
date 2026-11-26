-- Prove2me | solution 1 for Stanley.eval_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:55.584897+00:00
-- url     : https://prove2.me/submissions/6922e321-dc37-499a-91b6-b13e499d7b2c

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_eval_card

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution (n m : ℕ) :
    (chromaticPolynomial G).eval ((n : ℤ) + m) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval (n : ℤ) *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ) := by
  classical
  have h := Fintype.card_congr (colorSumEquiv (α := Fin n) (β := Fin m) G)
  rw [Fintype.card_sigma] at h
  simpa [Fintype.card_prod, ← eval_card, Fintype.card_sum, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun k : ℕ => (k : ℤ)) h.symm
end Stanley
