-- Prove2me | solution 1 for Psi.noDD_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:45:12.450804+00:00
-- url     : https://prove2.me/submissions/8352b5f9-7c1c-4226-a3be-259f366f0072

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_hasDD_cons


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution : ∀ (k : ℕ) (r : List Bool) (h : ℤ), r.length = k → 2 ≤ h →
    validFrom r h → runHeight r h = 0 → hasDD r = false → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro r h hlen hh hv he hdd
    cases r with
    | nil => simp only [runHeight] at he; omega
    | cons x r' =>
        cases x with
        | true =>
            refine IH r'.length (by simp only [List.length_cons] at hlen; omega) r' (h + 1) rfl
              (by omega) ?_ ?_ ?_
            · simpa only [validFrom] using hv
            · simpa only [runHeight] using he
            · rw [hasDD_cons] at hdd; simpa using hdd
        | false =>
            simp only [validFrom] at hv
            obtain ⟨_, hv'⟩ := hv
            simp only [runHeight] at he
            rw [hasDD_cons] at hdd
            have hddr' := (Bool.or_eq_false_iff.mp hdd).2
            have hjunc := (Bool.or_eq_false_iff.mp hdd).1
            by_cases hh2 : 2 ≤ h - 1
            · exact IH r'.length (by simp only [List.length_cons] at hlen; omega) r' (h - 1) rfl
                hh2 hv' he hddr'
            · have hh1 : h - 1 = 1 := by omega
              rw [hh1] at hv' he
              cases r' with
              | nil => simp only [runHeight] at he; omega
              | cons y ys =>
                  have hy : y = true := by
                    simp only [List.head?_cons] at hjunc
                    cases y with | false => simp at hjunc | true => rfl
                  subst hy
                  refine IH ys.length (by simp only [List.length_cons] at hlen; omega) ys 2 rfl
                    (by omega) ?_ ?_ ?_
                  · simpa [validFrom] using hv'
                  · simpa [runHeight] using he
                  · rw [hasDD_cons] at hddr'; simpa using hddr'
end Psi
