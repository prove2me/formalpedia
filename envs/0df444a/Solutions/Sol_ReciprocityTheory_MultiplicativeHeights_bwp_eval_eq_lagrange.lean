-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_eval_eq_lagrange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:22.977836+00:00
-- url     : https://prove2.me/submissions/e2cdd9c9-1458-490c-bf44-e834407e9ba1

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (S : Finset ℂ) (Q : ℂ[X]) (k : ℕ) (hS : S.card = k + 1)
    (hQ : Q.natDegree ≤ k) (x : ℂ) :
    Q.eval x = ∑ c ∈ S, (Lagrange.basis S id c).eval x * Q.eval c := by
  have hinj : Set.InjOn id (S : Set ℂ) := Function.injective_id.injOn
  have hdeg : Q.degree < S.card := by
    rw [hS]
    calc Q.degree ≤ (k : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hQ
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [mul_comm]
end ReciprocityTheory.MultiplicativeHeights
