-- Prove2me | solution 1 for Stanley.polynomial_ext_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:50.02028+00:00
-- url     : https://prove2.me/submissions/a41b204d-6c1b-4cf5-adde-0031199eb7f3

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution (p q : ℤ[X])
    (h : ∀ n : ℕ, p.eval (n : ℤ) = q.eval (n : ℤ)) : p = q := by
  apply p.eq_of_infinite_eval_eq q
  apply (Set.infinite_range_of_injective Int.ofNat_injective).mono
  rintro _ ⟨n, rfl⟩
  exact h n
end Stanley
