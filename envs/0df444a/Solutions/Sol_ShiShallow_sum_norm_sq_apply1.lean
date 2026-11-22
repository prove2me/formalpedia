-- Prove2me | solution 1 for ShiShallow.sum_norm_sq_apply1
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:33:41.258822+00:00
-- url     : https://prove2.me/submissions/7012bc32-8457-4b81-905a-fa54190e7000

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Theorems.Thm_ShiShallow_apply1_at_fibre
import Theorems.Thm_ShiShallow_sum_norm_sq_mulVec

section
open ShiShallow

theorem solution {n : ℕ} {U : Matrix Bool Bool ℂ}
    (hU : U.conjTranspose * U = 1) (i : Fin n) (ψ : QState n) :
    ∑ x : Bits n, ‖apply1 U i ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  classical
  set e := Equiv.funSplitAt i Bool with he
  have hL : ∑ x : Bits n, ‖apply1 U i ψ x‖ ^ 2
      = ∑ p : Bool × ({j : Fin n // j ≠ i} → Bool), ‖apply1 U i ψ (e.symm p)‖ ^ 2 :=
    Fintype.sum_equiv e _ _ (fun x => by simp)
  have hR : ∑ x : Bits n, ‖ψ x‖ ^ 2
      = ∑ p : Bool × ({j : Fin n // j ≠ i} → Bool), ‖ψ (e.symm p)‖ ^ 2 :=
    Fintype.sum_equiv e _ _ (fun x => by simp)
  rw [hL, hR, Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm (s := (Finset.univ : Finset Bool)), 
      Finset.sum_comm (s := (Finset.univ : Finset Bool))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [he, apply1_at_fibre]
  exact sum_norm_sq_mulVec hU (fun b => ψ ((Equiv.funSplitAt i Bool).symm (b, r)))

end
