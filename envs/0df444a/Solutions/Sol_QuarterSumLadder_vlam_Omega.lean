-- Prove2me | solution 1 for QuarterSumLadder.vlam_Omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:45.467068+00:00
-- url     : https://prove2.me/submissions/9536909c-9d9a-40db-af26-296054a52496

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_vlam_eq_of_dvd
public import Theorems.Thm_QuarterSumLadder_le_vlam_of_dvd
public import Theorems.Thm_QuarterSumLadder_first_thresholds
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime] {χ : MulChar (ZMod p) GaussianInt}
  (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) := by
  obtain ⟨a, b, c⟩ := first_thresholds hp8 hχ
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 hz => ?_⟩
  · obtain ⟨h1, h2⟩ := a hw; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · obtain ⟨h1, h2⟩ := b hw h16; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · exact le_vlam_of_dvd hz (by simpa using c hw h16)
end QuarterSumLadder
