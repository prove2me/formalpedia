-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_sepPoly_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:06.457552+00:00
-- url     : https://prove2.me/submissions/a6f89faa-7488-41a0-b508-d3027212ca68

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_exists_nodes
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_eq_lagrange
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_aeval_X

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
theorem _root_.solution (k : ℕ) : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) →
    ∃ F : MvPolynomial (Fin n) ℂ, ∀ y, G y = MvPolynomial.eval y F
  | 0, G, _ => ⟨MvPolynomial.C (G 0), fun y => by
      rw [MvPolynomial.eval_C, Subsingleton.elim y 0]⟩
  | n + 1, G, hG => by
    obtain ⟨S, hS, -⟩ := bwp_exists_nodes ∅ Set.finite_empty k
    have hsub : ∀ c : ℂ, ∃ F : MvPolynomial (Fin n) ℂ,
        ∀ y', G (Fin.cons c y') = MvPolynomial.eval y' F := by
      intro c
      refine solution k n (fun y' => G (Fin.cons c y')) ?_
      intro y' m
      obtain ⟨Q, hQ, hQt⟩ := hG (Fin.cons c y') m.succ
      exact ⟨Q, hQ, fun t => by simp only [Fin.cons_update]; exact hQt t⟩
    choose Fc hFc using hsub
    refine ⟨∑ c ∈ S, Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis S id c) *
      MvPolynomial.rename Fin.succ (Fc c), fun y => ?_⟩
    obtain ⟨Q, hQ, hQt⟩ := hG y 0
    have hy : ∀ t, Function.update y 0 t = Fin.cons t (Fin.tail y) := by
      intro t
      conv_lhs => rw [← Fin.cons_self_tail y]
      exact Fin.update_cons_zero _ _ _
    have h1 : G y = Q.eval (y 0) := by
      rw [← hQt]; simp
    rw [h1, bwp_eval_eq_lagrange S Q k hS hQ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, bwp_eval_aeval_X, MvPolynomial.eval_rename, ← hQt c, hy c, hFc c]
    rfl
end ReciprocityTheory.MultiplicativeHeights
