-- Prove2me | solution 1 for ThreeSum1960614.executable_scale_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:27:07.752254+00:00
-- url     : https://prove2.me/submissions/e257a586-5513-44f9-b364-9756720bf87d

import Definitions.Def_ThreeSum1960614_Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open ThreeSum1960614 ThreeSum1960614.Schedule

theorem solution (m : ℕ) :
    2 ∣ microSize m ∧ 20 ∣ blockCount m ∧
    (0 < microSize m →
      0 ≤ epsilon * (m : ℝ) - totalSize m ∧
      epsilon * (m : ℝ) - totalSize m < 20 * microSize m) ∧
    0 ≤ (-beta) * (totalSize m : ℝ) - bandExponent m ∧
    (-beta) * (totalSize m : ℝ) - bandExponent m < 1 ∧
    0 < bandDivisor m := by
  refine ⟨⟨Nat.nthRoot 3 m / 2, rfl⟩,
    ⟨203889696 * m / (20000000000 * microSize m), rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro hs
    have hd : 0 < 20000000000 * microSize m := by positivity
    have hmod := Nat.mod_lt (203889696 * m) hd
    have hdiv := Nat.mod_add_div (203889696 * m) (20000000000 * microSize m)
    have heq : 20000000000 * microSize m *
        (203889696 * m / (20000000000 * microSize m)) = 1000000000 * totalSize m := by
      dsimp [totalSize, blockCount]
      ring
    rw [heq] at hdiv
    have hlo : 1000000000 * totalSize m ≤ 203889696 * m := by omega
    have hhi : 203889696 * m < 1000000000 * totalSize m + 20000000000 * microSize m := by omega
    have hlor : (1000000000 : ℝ) * totalSize m ≤ 203889696 * m := by exact_mod_cast hlo
    have hhir : (203889696 : ℝ) * m < 1000000000 * totalSize m + 20000000000 * microSize m := by
      exact_mod_cast hhi
    dsimp [epsilon]
    constructor <;> linarith
  · have h := Nat.div_mul_le_self (62656016 * totalSize m) 1000000000
    have hr : (bandExponent m : ℝ) * 1000000000 ≤ 62656016 * totalSize m := by
      exact_mod_cast h
    dsimp [beta]
    linarith
  · have hmod := Nat.mod_lt (62656016 * totalSize m) (by decide : 0 < 1000000000)
    have hdiv := Nat.mod_add_div (62656016 * totalSize m) 1000000000
    have h : 62656016 * totalSize m < 1000000000 * bandExponent m + 1000000000 := by
      dsimp [bandExponent]
      omega
    have hr : (62656016 : ℝ) * totalSize m < 1000000000 * bandExponent m + 1000000000 := by
      exact_mod_cast h
    dsimp [beta]
    linarith
  · dsimp [bandDivisor]
    positivity

#print axioms solution
