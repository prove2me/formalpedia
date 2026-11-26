-- Prove2me | solution 1 for SemigroupBetti.beta1_le_two_mul_normalizedWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:25:58.010214+00:00
-- url     : https://prove2.me/submissions/e78d7819-8419-4a5c-b9a7-12b7d80dd582

module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Definitions.Def_SemigroupBetti
public import Definitions.Def_SemigroupBetti_Solution
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W
public import Theorems.Thm_SemigroupBetti_GenData_ofChallenge_n
public import Theorems.Thm_SemigroupBetti_GenData_spanRank_le_beta1_of_n_eq


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open MvPolynomial
namespace SemigroupBetti
theorem _root_.solution (K : Type*) [Field K] (n : Fin 4 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n) (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n) :
    (toricIdeal K n).spanRank ≤ (2 * normalizedWidth n : ℕ) := by
  let G := GenData.ofChallenge n hpos hmono hgcd hmin
  have hb : (toricIdeal K n).spanRank ≤ (G.beta1 : Cardinal) :=
    G.spanRank_le_beta1_of_n_eq K (GenData.ofChallenge_n n hpos hmono hgcd hmin)
  have hW : normalizedWidth n = G.W := rfl
  refine hb.trans ?_
  rw [hW]
  exact_mod_cast G.beta1_le_two_W
end SemigroupBetti
