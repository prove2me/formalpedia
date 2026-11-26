-- Prove2me | solution 1 for SemigroupBetti.beta1_le_two_mul_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:28:26.520347+00:00
-- url     : https://prove2.me/submissions/9499ec7c-c8c4-47b4-ad13-c3d773da759e

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
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_w
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
    (toricIdeal K n).spanRank ≤ (2 * (n 3 - n 0) : ℕ) := by
  let G := GenData.ofChallenge n hpos hmono hgcd hmin
  have hb : (toricIdeal K n).spanRank ≤ (G.beta1 : Cardinal) :=
    G.spanRank_le_beta1_of_n_eq K (GenData.ofChallenge_n n hpos hmono hgcd hmin)
  have hw : n 3 - n 0 = G.w := rfl
  refine hb.trans ?_
  rw [hw]
  exact_mod_cast G.beta1_le_two_w
end SemigroupBetti
