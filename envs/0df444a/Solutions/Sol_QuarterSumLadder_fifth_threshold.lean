-- Prove2me | solution 1 for QuarterSumLadder.fifth_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:03.789396+00:00
-- url     : https://prove2.me/submissions/e1c6b2af-3196-441a-8245-5cb998d1c209

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_norm_eq
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_sixteen_dvd_iff
public import Theorems.Thm_QuarterSumLadder_sum_R
public import Theorems.Thm_QuarterSumLadder_thirtytwo_dvd_iff


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
    ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔
        (32 : ℤ) ∣ 2 * (Omega χ).norm ∧ ((R χ 2 + R χ 3 : ℕ) : ℤ) % 4 = ((Q p / 2 : ℕ) : ℤ) % 4) ∧
      ((32 : ℤ) ∣ 2 * (Omega χ).norm →
        ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im)) := by
  have hs := sum_R hp8 hχ
  have hpq := mod_eight_aux hp8
  have hQ : 2 ∣ Q p := by unfold Q; omega
  have hxy : (Omega χ).re + (Omega χ).im = (Q p : ℤ) - 2 * ((R χ 2 : ℤ) + R χ 3) := by
    show ((R χ 0 : ℤ) - R χ 2) + ((R χ 1 : ℤ) - R χ 3) = _
    have : (R χ 0 + R χ 1 + R χ 2 + R χ 3 : ℤ) = Q p := by exact_mod_cast hs
    linarith
  have h32 : (32 : ℤ) ∣ 2 * (Omega χ).norm ↔ (16 : ℤ) ∣ (Omega χ).norm := by omega
  have h64 : (64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (32 : ℤ) ∣ (Omega χ).norm := by omega
  have key : (32 : ℤ) ∣ 2 * (Omega χ).norm →
      ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im) := by
    intro h
    rw [h32, norm_eq, sixteen_dvd_iff] at h
    rw [h64, norm_eq]
    exact thirtytwo_dvd_iff h.1 h.2
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, key⟩
  · have h' : (32 : ℤ) ∣ 2 * (Omega χ).norm := by omega
    refine ⟨h', ?_⟩
    have := (key h').1 h
    rw [hxy] at this
    obtain ⟨k, hk⟩ := hQ
    push_cast [hk]; omega
  · refine (key h.1).2 ?_
    rw [hxy]
    obtain ⟨k, hk⟩ := hQ
    have := h.2; push_cast [hk] at this ⊢; omega
end QuarterSumLadder
