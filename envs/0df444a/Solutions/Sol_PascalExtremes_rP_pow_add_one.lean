-- Prove2me | solution 1 for PascalExtremes.rP_pow_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:37.104675+00:00
-- url     : https://prove2.me/submissions/c296504e-4d24-4fcb-96fd-c6c349db55b0

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p a : ℕ} (hp : 1 < p) (ha : 1 ≤ a) :
    rP p (p ^ a + 1) = a + 1 := by
  have hpa : p ≤ p ^ a := by
    calc
      p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have hgap : p ^ a + 1 < p ^ (a + 1) := by
    calc
      p ^ a + 1 < p ^ a + p ^ a := Nat.add_lt_add_left (by omega) _
      _ = 2 * p ^ a := by omega
      _ ≤ p * p ^ a := Nat.mul_le_mul_right _ hp
      _ = p ^ (a + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hlog :
      Nat.log p (p ^ a + 1) = a :=
    Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) hgap
  simp [rP, hlog]
end PascalExtremes
