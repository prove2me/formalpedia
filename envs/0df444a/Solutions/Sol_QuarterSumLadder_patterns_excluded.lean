-- Prove2me | solution 1 for QuarterSumLadder.patterns_excluded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:20.808089+00:00
-- url     : https://prove2.me/submissions/752eead5-2422-4687-b79d-2ca47ed3a88c

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_orbit_parity
public import Theorems.Thm_QuarterSumLadder_char_two


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) := by
  rcases char_two hp8 hχ with hw | hw
  · have := orbit_parity hp8 hχ hw
    constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;> omega
  · have hq := quarter_law hp8 hχ
    rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;> omega
end QuarterSumLadder
