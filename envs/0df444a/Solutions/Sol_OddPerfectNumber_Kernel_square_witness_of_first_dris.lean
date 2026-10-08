-- Prove2me | solution 1 for OddPerfectNumber.Kernel.square_witness_of_first_dris
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:05:53.321341+00:00
-- url     : https://prove2.me/submissions/ce75f045-7a01-4a3d-ab8f-cedea73adbda

-- Repair of candidate 7365 (1 group L43, full report read).
-- Root cause: the PUBLISHED square-cancel statement uses EXPLICIT binders
-- (d S y : Nat) (an authoring-side effect of the U+2260 scanner fix), so the call
-- filled d with hd1. Fix: supply d1 _ _ explicitly. Second mismatch: hd1/hS0 are
-- Prop Ne while the target takes Bool bne-true hypotheses; bridge with simpa
-- (reverse direction verified in solutionA/V2 via simpa using hp2).
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSquare_of_sq_mul_eq_sq

theorem solution (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2)
    (hm : Odd m)
    (hq : q.Prime) (hr : r.Prime)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    exists y : Nat,
      y ^ 2 = q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) := by
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have h1' : 2 * m ^ 2 =
      2 * (d1 ^ 2 * (q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)))) := by
    rw [h1]
    ring
  have hm2 : m ^ 2 =
      d1 ^ 2 * (q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) :=
    Nat.mul_left_cancel (show (0 : Nat) < 2 by norm_num) h1'
  have hd1 : d1 ≠ 0 := by
    intro hz
    apply hm0
    have h0 : m ^ 2 = 0 := by
      rw [hm2, hz]
      simp
    rwa [sq_eq_zero_iff] at h0
  have hq0 : q ≠ 0 := hq.ne_zero
  have hr0 : r ≠ 0 := hr.ne_zero
  have hC : p ^ 2 + p + 1 ≠ 0 := by positivity
  have hX : (p + 1) / 2 ≠ 0 := by
    have h2 : 2 ≤ p + 1 := by
      have hpl := hp.two_le
      omega
    omega
  have hD : p ^ 2 - p + 1 ≠ 0 := by omega
  have hS0 : q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq0 hr0) hC) (mul_ne_zero hX hD)
  have hd1b : d1 != 0 := by simpa using hd1
  have hS0b : q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) != 0 := by
    simpa using hS0
  have hSq :=
    OddPerfectNumber.Kernel.isSquare_of_sq_mul_eq_sq d1 _ _ hd1b hS0b hm2.symm
  obtain ⟨w, hw⟩ := hSq
  exact ⟨w, by rw [hw, pow_two]⟩
