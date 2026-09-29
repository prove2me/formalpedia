-- Prove2me | solution 1 for OddPerfectNumber.opnRightRay_mod_five_period_three
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T10:17:24.991974+00:00
-- url     : https://prove2.me/submissions/a7ed9a41-4449-4497-9d69-a84517c27122

import Mathlib
import Definitions.Def_opnRightRay
import Theorems.Thm_OddPerfectNumber_opnRightRay_recurrence

open OddPerfectNumber

theorem solution (m : Nat) :
    opnRightRay (3 * m) % 5 = 1 ∧
      opnRightRay (3 * m + 1) % 5 = 2 ∧
      opnRightRay (3 * m + 2) % 5 = 1 := by
  induction m with
  | zero =>
      norm_num [opnRightRay]
  | succ m ih =>
      rcases ih with ⟨h0m, h1m, h2m⟩
      have h0 := opnRightRay_recurrence (3 * m + 1)
      have h1 := opnRightRay_recurrence (3 * m + 2)
      have h2 := opnRightRay_recurrence (3 * m + 3)
      have h0' :
          opnRightRay (3 * m + 3) + opnRightRay (3 * m + 1) + 1 =
            9 * opnRightRay (3 * m + 2) := by
        convert h0 using 1 <;> omega
      have h1' :
          opnRightRay (3 * m + 4) + opnRightRay (3 * m + 2) + 1 =
            9 * opnRightRay (3 * m + 3) := by
        convert h1 using 1 <;> omega
      have h2' :
          opnRightRay (3 * m + 5) + opnRightRay (3 * m + 3) + 1 =
            9 * opnRightRay (3 * m + 4) := by
        convert h2 using 1 <;> omega
      have h1mod : opnRightRay (3 * m + 1) ≡ 2 [MOD 5] := by
        simpa [Nat.ModEq] using h1m
      have h2mod : opnRightRay (3 * m + 2) ≡ 1 [MOD 5] := by
        simpa [Nat.ModEq] using h2m
      have hrec0mod :
          opnRightRay (3 * m + 3) + opnRightRay (3 * m + 1) + 1 ≡
            9 * opnRightRay (3 * m + 2) [MOD 5] := by
        rw [h0']
      have htmp0 := hrec0mod.trans (h2mod.mul_left 9)
      have htmp1 := h1mod.add_right 1
      have htmp2 : opnRightRay (3 * m + 3) +
          (opnRightRay (3 * m + 1) + 1) ≡
            opnRightRay (3 * m + 3) + (2 + 1) [MOD 5] :=
        Nat.ModEq.rfl.add htmp1
      have htmp2' : opnRightRay (3 * m + 3) +
          opnRightRay (3 * m + 1) + 1 ≡
            opnRightRay (3 * m + 3) + (2 + 1) [MOD 5] := by
        simpa [Nat.add_assoc] using htmp2
      have htmp3 := htmp2'.symm.trans htmp0
      have htmp4 : opnRightRay (3 * m + 3) + (2 + 1) ≡
          1 + 3 [MOD 5] := by
        exact htmp3.trans (by norm_num [Nat.ModEq])
      have hnew0mod : opnRightRay (3 * m + 3) ≡ 1 [MOD 5] := by
        apply Nat.ModEq.add_right_cancel' 3
        simpa [Nat.add_assoc] using htmp4
      have hnew0 : opnRightRay (3 * m + 3) % 5 = 1 := by
        simpa [Nat.ModEq] using hnew0mod
      have hrec1mod :
          opnRightRay (3 * m + 4) + opnRightRay (3 * m + 2) + 1 ≡
            9 * opnRightRay (3 * m + 3) [MOD 5] := by
        rw [h1']
      have htmp5 := hrec1mod.trans (hnew0mod.mul_left 9)
      have htmp6 := h2mod.add_right 1
      have htmp7 : opnRightRay (3 * m + 4) +
          (opnRightRay (3 * m + 2) + 1) ≡
            opnRightRay (3 * m + 4) + (1 + 1) [MOD 5] :=
        Nat.ModEq.rfl.add htmp6
      have htmp7' : opnRightRay (3 * m + 4) +
          opnRightRay (3 * m + 2) + 1 ≡
            opnRightRay (3 * m + 4) + (1 + 1) [MOD 5] := by
        simpa [Nat.add_assoc] using htmp7
      have htmp8 := htmp7'.symm.trans htmp5
      have htmp9 : opnRightRay (3 * m + 4) + (1 + 1) ≡
          2 + 2 [MOD 5] := by
        exact htmp8.trans (by norm_num [Nat.ModEq])
      have hnew1mod : opnRightRay (3 * m + 4) ≡ 2 [MOD 5] := by
        apply Nat.ModEq.add_right_cancel' 2
        simpa [Nat.add_assoc] using htmp9
      have hnew1 : opnRightRay (3 * m + 4) % 5 = 2 := by
        simpa [Nat.ModEq] using hnew1mod
      have hrec2mod :
          opnRightRay (3 * m + 5) + opnRightRay (3 * m + 3) + 1 ≡
            9 * opnRightRay (3 * m + 4) [MOD 5] := by
        rw [h2']
      have htmp10 := hrec2mod.trans (hnew1mod.mul_left 9)
      have htmp11 := hnew0mod.add_right 1
      have htmp12 : opnRightRay (3 * m + 5) +
          (opnRightRay (3 * m + 3) + 1) ≡
            opnRightRay (3 * m + 5) + (1 + 1) [MOD 5] :=
        Nat.ModEq.rfl.add htmp11
      have htmp12' : opnRightRay (3 * m + 5) +
          opnRightRay (3 * m + 3) + 1 ≡
            opnRightRay (3 * m + 5) + (1 + 1) [MOD 5] := by
        simpa [Nat.add_assoc] using htmp12
      have htmp13 := htmp12'.symm.trans htmp10
      have htmp14 : opnRightRay (3 * m + 5) + (1 + 1) ≡
          1 + 2 [MOD 5] := by
        exact htmp13.trans (by norm_num [Nat.ModEq])
      have hnew2mod : opnRightRay (3 * m + 5) ≡ 1 [MOD 5] := by
        apply Nat.ModEq.add_right_cancel' 2
        simpa [Nat.add_assoc] using htmp14
      have hnew2 : opnRightRay (3 * m + 5) % 5 = 1 := by
        simpa [Nat.ModEq] using hnew2mod
      have hres :
          opnRightRay (3 * m + 3) % 5 = 1 ∧
            opnRightRay (3 * m + 4) % 5 = 2 ∧
            opnRightRay (3 * m + 5) % 5 = 1 := by
        exact ⟨hnew0, hnew1, hnew2⟩
      refine ⟨?_, ?_, ?_⟩
      · have hi0 : 3 * Nat.succ m = 3 * m + 3 := by omega
        rw [hi0]
        exact hres.1
      · have hi1 : 3 * Nat.succ m + 1 = 3 * m + 4 := by omega
        rw [hi1]
        exact hres.2.1
      · have hi2 : 3 * Nat.succ m + 2 = 3 * m + 5 := by omega
        rw [hi2]
        exact hres.2.2
