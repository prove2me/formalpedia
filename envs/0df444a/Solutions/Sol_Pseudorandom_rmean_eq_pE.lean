-- Prove2me | solution 1 for Pseudorandom.rmean_eq_pE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:20.435235+00:00
-- url     : https://prove2.me/submissions/8c95a0a8-dfb4-474f-9bce-c979d248b005

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]
namespace Pseudorandom
theorem _root_.solution : ∀ {n : ℕ} (P : Fin n → α → ℝ) (f : (Fin n → α) → ℝ),
    rmean P f = pE P f
  | 0, P, f => by
    simp only [rmean, pE, pw, univ_eq_empty, prod_empty, one_mul]
    rw [Fintype.sum_unique]
    congr 1
  | n + 1, P, f => by
    simp only [rmean]
    simp_rw [solution]
    unfold pE
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => α) (fun x => pw P (Fin.cons x.1 x.2) *
      f (Fin.cons x.1 x.2)) _ (fun x => rfl)]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    simp only [pw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring
end Pseudorandom
