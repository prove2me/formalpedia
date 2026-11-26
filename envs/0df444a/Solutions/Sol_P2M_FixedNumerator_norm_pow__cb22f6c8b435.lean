-- Prove2me | solution 1 for P2M_FixedNumerator_norm_pow__cb22f6c8b435
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:00.251301+00:00
-- url     : https://prove2.me/submissions/4c9db2e2-2448-44d9-a1b4-6f19635563ce

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (a : GaussianInt) (k : ℕ) : (a ^ k).norm = a.norm ^ k := by
  induction k with
  | zero => simp [Zsqrtd.norm]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]
end FixedNumerator
