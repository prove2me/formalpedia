-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_dvd_two_mul_add_one_of_even_gives_c_residue
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:24:05.226583+00:00
-- url     : https://prove2.me/submissions/af7b1d33-a1d1-4d94-b076-0619827dbfdf

import Mathlib

namespace OPNCex73123563

/-- `a = 2`, `c = 1`: `5 ∣ 2 + 2 + 1 = 5`, but `(1 + 2 + 3) % 5 = 1`. -/
theorem cex :
    ¬ (∀ (a c : Nat), Even a → Dvd.dvd 5 (a + 2 * c + 1) → (c + a + 3) % 5 = 0) := by
  intro h
  have := h 2 1 ⟨1, rfl⟩ ⟨1, rfl⟩
  omega

end OPNCex73123563

theorem solution : ¬ (∀ (a c : Nat) (ha : Even a) (h5 : Dvd.dvd 5 (a + 2 * c + 1)),
    (c + a + 3) % 5 = 0) := by
  exact OPNCex73123563.cex
