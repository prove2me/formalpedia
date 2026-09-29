-- Prove2me | solution 1 for OddPerfectNumber.opnRightRay_parity_period_three
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T10:16:31.171612+00:00
-- url     : https://prove2.me/submissions/f6f7c08b-8a1d-4a1c-803f-883bb8ee944c

import Mathlib
import Definitions.Def_opnRightRay
import Theorems.Thm_OddPerfectNumber_opnRightRay_recurrence

open OddPerfectNumber

theorem solution (m : Nat) :
    Odd (opnRightRay (3 * m)) ∧
      Even (opnRightRay (3 * m + 1)) ∧
      Even (opnRightRay (3 * m + 2)) := by
  induction m with
  | zero =>
      norm_num [opnRightRay]
  | succ m ih =>
      have ha : Odd (opnRightRay (3 * m)) := ih.1
      have hb : Even (opnRightRay (3 * m + 1)) := ih.2.1
      have hc : Even (opnRightRay (3 * m + 2)) := ih.2.2
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
      have odd_of_even_add_odd {u v : Nat} (hs : Even (u + v))
          (hv : Odd v) : Odd u := by
        apply Nat.not_even_iff_odd.mp
        intro hu
        exact (Nat.not_even_iff_odd.mpr hv) ((Nat.even_add.mp hs).mp hu)
      have even_of_odd_add_odd {u v : Nat} (hs : Odd (u + v))
          (hv : Odd v) : Even u := by
        apply Nat.not_odd_iff_even.mp
        intro hu
        exact (Nat.not_even_iff_odd.mpr hs) (hu.add_odd hv)
      have even_of_even_add_even {u v : Nat} (hs : Even (u + v))
          (hv : Even v) : Even u :=
        (Nat.even_add.mp hs).mpr hv
      have hsum0 : Even (opnRightRay (3 * m + 3) +
          (opnRightRay (3 * m + 1) + 1)) := by
        have hh : Even (opnRightRay (3 * m + 3) +
            opnRightRay (3 * m + 1) + 1) := by
          rw [h0']
          exact hc.mul_left 9
        simpa [Nat.add_assoc] using hh
      have hnew0 : Odd (opnRightRay (3 * m + 3)) :=
        odd_of_even_add_odd hsum0 hb.add_one
      have hsum1 : Odd (opnRightRay (3 * m + 4) +
          (opnRightRay (3 * m + 2) + 1)) := by
        have hh : Odd (opnRightRay (3 * m + 4) +
            opnRightRay (3 * m + 2) + 1) := by
          rw [h1']
          exact (by norm_num : Odd 9).mul hnew0
        simpa [Nat.add_assoc] using hh
      have hnew1 : Even (opnRightRay (3 * m + 4)) :=
        even_of_odd_add_odd hsum1 hc.add_one
      have hsum2 : Even (opnRightRay (3 * m + 5) +
          (opnRightRay (3 * m + 3) + 1)) := by
        have hh : Even (opnRightRay (3 * m + 5) +
            opnRightRay (3 * m + 3) + 1) := by
          rw [h2']
          exact hnew1.mul_left 9
        simpa [Nat.add_assoc] using hh
      have hnew2 : Even (opnRightRay (3 * m + 5)) :=
        even_of_even_add_even hsum2 hnew0.add_one
      have hres :
          Odd (opnRightRay (3 * m + 3)) ∧
            Even (opnRightRay (3 * m + 4)) ∧
            Even (opnRightRay (3 * m + 5)) := by
        refine ⟨?_, ?_, ?_⟩
        · exact hnew0
        · exact hnew1
        · exact hnew2
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
