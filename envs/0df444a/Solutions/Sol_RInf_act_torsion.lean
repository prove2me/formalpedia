-- Prove2me | solution 1 for RInf.act_torsion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:51.253633+00:00
-- url     : https://prove2.me/submissions/1a44eba5-bf01-4c93-9306-bfffe6f825bf

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid
open RInf

theorem g74p_rep_pow {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (σ : Equiv.Perm (Fin (n + 1))) (k : Nat) (q : Q) :
    W.rep (σ ^ k) q = ((fun x => W.rep σ x)^[k]) q := by
  induction k with
  | zero => simp [W.rep_one]
  | succ k ih =>
    rw [pow_succ, W.rep_mul, Function.iterate_succ_apply', ← ih]
    rfl

theorem solution {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (α : P ≃* P) :
    ∃ m : Nat, 0 < m ∧ ∀ q : Q, ((fun x => W.act α x)^[m]) q = q := by
  obtain ⟨σ, hσ⟩ := W.factor α
  refine ⟨orderOf σ, orderOf_pos σ, fun q => ?_⟩
  rw [hσ, ← g74p_rep_pow, pow_orderOf_eq_one, W.rep_one]
  rfl
