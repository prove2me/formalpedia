-- Prove2me | solution 1 for QuarterSumLadder.vlam_B2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:13.063686+00:00
-- url     : https://prove2.me/submissions/57d92771-2b93-4df9-a642-05c2310d72a3

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_b2_trichotomy
public import Theorems.Thm_QuarterSumLadder_vlam_eq_of_dvd
public import Theorems.Thm_QuarterSumLadder_le_vlam_of_dvd
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
    (χ 2 = -1 → vlam (B2 χ) = 5) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (B2 χ) = 6) ∧
      (χ 2 = 1 → p % 16 = 1 → B2 χ ≠ 0 → 7 ≤ vlam (B2 χ)) := by
  obtain ⟨a, b, c⟩ := b2_trichotomy hp8 hχ
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 hz => ?_⟩
  · obtain ⟨h1, h2⟩ := a hw; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · obtain ⟨h1, h2⟩ := b hw h16; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · exact le_vlam_of_dvd hz (by simpa using c hw h16)
end QuarterSumLadder
