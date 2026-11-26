-- Prove2me | solution 1 for PascalExtremes.mul_q0_eq_pow_three_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:22.873608+00:00
-- url     : https://prove2.me/submissions/25691310-8013-40b7-ab95-cb609af02200

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (p ^ a + 1) * q0 p a = p ^ (3 * a) + 1 := by
  let Q := p ^ a
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos hp.pos _
  have hQleQ2 : Q ≤ Q * Q := by
    nlinarith
  have hpow2 : p ^ (2 * a) = Q * Q := by
    dsimp [Q]
    rw [show 2 * a = a + a by omega, pow_add]
  have hpow3 : p ^ (3 * a) = Q * Q * Q := by
    dsimp [Q]
    rw [show 3 * a = a + a + a by omega, pow_add, pow_add]
  let S := Q * Q - Q
  have hS : Q + S = Q * Q := by
    dsimp [S]
    omega
  have hq : q0 p a = S + 1 := by
    dsimp [q0, S, Q]
    rw [hpow2]
  rw [hq, hpow3]
  have hS' : S + Q = Q * Q := by simpa [Nat.add_comm] using hS
  calc
    (Q + 1) * (S + 1) = Q * S + (Q + S) + 1 := by ring
    _ = Q * S + Q * Q + 1 := by rw [hS]
    _ = Q * (S + Q) + 1 := by ring
    _ = Q * (Q * Q) + 1 := by rw [hS']
    _ = Q * Q * Q + 1 := by ring
end PascalExtremes
