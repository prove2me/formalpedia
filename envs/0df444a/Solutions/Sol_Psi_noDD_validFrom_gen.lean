-- Prove2me | solution 1 for Psi.noDD_validFrom_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:45:53.609607+00:00
-- url     : https://prove2.me/submissions/3bd0015e-ed0b-4c01-8f56-51514eec5e05

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_hasDD_cons


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (ρ : List Bool) : ∀ (h : ℤ), 0 ≤ h → hasDD ρ = false →
    (ρ.head? = some false → 1 ≤ h) → validFrom ρ h := by
  induction ρ with
  | nil => intro h _ _ _; trivial
  | cons x r' ih =>
      intro h hh hdd hpre
      cases x with
      | true => simp only [validFrom]
                exact ih (h + 1) (by omega) (by rw [hasDD_cons] at hdd; simpa using hdd)
                  (fun _ => by omega)
      | false =>
          simp only [validFrom]
          have hjunc : r'.head? ≠ some false := by
            rw [hasDD_cons] at hdd
            have := (Bool.or_eq_false_iff.mp hdd).1
            intro hcon; rw [hcon] at this; simp at this
          have hh1 : 1 ≤ h := hpre (by simp)
          exact ⟨by omega, ih (h - 1) (by omega)
            (by rw [hasDD_cons] at hdd; exact (Bool.or_eq_false_iff.mp hdd).2)
            (fun hcon => absurd hcon hjunc)⟩
end Psi
