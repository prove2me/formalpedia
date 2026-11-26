-- Prove2me | solution 1 for QuarterSumLadder.coord_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:10.022169+00:00
-- url     : https://prove2.me/submissions/5c859fb8-c5d3-4185-a5b8-f092f08be2e4

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_orbit_parity
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_sum_R


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
    (χ 2 = -1 → (Omega χ).re % 2 = 1 ∧ (Omega χ).im % 2 = 1) ∧
      (χ 2 = 1 → (Omega χ).re % 2 = 0 ∧ (Omega χ).im % 2 = 0 ∧
        ((Omega χ).re - (Omega χ).im) % 4 = (Q p : ℤ) % 4) := by
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  have hre : (Omega χ).re = (R χ 0 : ℤ) - R χ 2 := rfl
  have him : (Omega χ).im = (R χ 1 : ℤ) - R χ 3 := rfl
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have hq := quarter_law hp8 hχ
    rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    rw [hre, him]; omega
  · obtain ⟨h1, h2, h3⟩ := orbit_parity hp8 hχ hw
    rw [hre, him]; omega
end QuarterSumLadder
