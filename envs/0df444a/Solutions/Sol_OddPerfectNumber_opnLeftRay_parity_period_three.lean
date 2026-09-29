-- Prove2me | solution 1 for OddPerfectNumber.opnLeftRay_parity_period_three
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T10:16:53.833722+00:00
-- url     : https://prove2.me/submissions/8ae5709a-fa94-4469-ad32-c633a11f6d43

import Mathlib
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_opnLeftRay_recurrence

open OddPerfectNumber

theorem solution (m : Nat) :
    Odd (opnLeftRay (3 * m)) ∧
      Even (opnLeftRay (3 * m + 1)) ∧
      Even (opnLeftRay (3 * m + 2)) := by
  induction m with
  | zero =>
      norm_num [opnLeftRay]
  | succ m ih =>
      have ha : Odd (opnLeftRay (3 * m)) := ih.1
      have hb : Even (opnLeftRay (3 * m + 1)) := ih.2.1
      have hc : Even (opnLeftRay (3 * m + 2)) := ih.2.2
      have h0 := opnLeftRay_recurrence (3 * m + 1)
      have h1 := opnLeftRay_recurrence (3 * m + 2)
      have h2 := opnLeftRay_recurrence (3 * m + 3)
      have h0' :
          opnLeftRay (3 * m + 3) + opnLeftRay (3 * m + 1) + 1 =
            9 * opnLeftRay (3 * m + 2) := by
        convert h0 using 1 <;> omega
      have h1' :
          opnLeftRay (3 * m + 4) + opnLeftRay (3 * m + 2) + 1 =
            9 * opnLeftRay (3 * m + 3) := by
        convert h1 using 1 <;> omega
      have h2' :
          opnLeftRay (3 * m + 5) + opnLeftRay (3 * m + 3) + 1 =
            9 * opnLeftRay (3 * m + 4) := by
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
      have hsum0 : Even (opnLeftRay (3 * m + 3) +
          (opnLeftRay (3 * m + 1) + 1)) := by
        have hh : Even (opnLeftRay (3 * m + 3) +
            opnLeftRay (3 * m + 1) + 1) := by
          rw [h0']
          exact hc.mul_left 9
        simpa [Nat.add_assoc] using hh
      have hnew0 : Odd (opnLeftRay (3 * m + 3)) :=
        odd_of_even_add_odd hsum0 hb.add_one
      have hsum1 : Odd (opnLeftRay (3 * m + 4) +
          (opnLeftRay (3 * m + 2) + 1)) := by
        have hh : Odd (opnLeftRay (3 * m + 4) +
            opnLeftRay (3 * m + 2) + 1) := by
          rw [h1']
          exact (by norm_num : Odd 9).mul hnew0
        simpa [Nat.add_assoc] using hh
      have hnew1 : Even (opnLeftRay (3 * m + 4)) :=
        even_of_odd_add_odd hsum1 hc.add_one
      have hsum2 : Even (opnLeftRay (3 * m + 5) +
          (opnLeftRay (3 * m + 3) + 1)) := by
        have hh : Even (opnLeftRay (3 * m + 5) +
            opnLeftRay (3 * m + 3) + 1) := by
          rw [h2']
          exact hnew1.mul_left 9
        simpa [Nat.add_assoc] using hh
      have hnew2 : Even (opnLeftRay (3 * m + 5)) :=
        even_of_even_add_even hsum2 hnew0.add_one
      have hres :
          Odd (opnLeftRay (3 * m + 3)) ∧
            Even (opnLeftRay (3 * m + 4)) ∧
            Even (opnLeftRay (3 * m + 5)) := by
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
