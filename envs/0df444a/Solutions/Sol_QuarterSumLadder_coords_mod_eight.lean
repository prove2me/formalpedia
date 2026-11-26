-- Prove2me | solution 1 for QuarterSumLadder.coords_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:27.532088+00:00
-- url     : https://prove2.me/submissions/25fa0a3a-7bb8-4622-a551-74953bc70d4d

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_weight_two_congruence
public import Theorems.Thm_QuarterSumLadder_E_sums
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
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
    c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] := by
  obtain ⟨h0, h1, -⟩ := weight_two_congruence hp8 hχ
  obtain ⟨e1, e2⟩ := E_sums hp8 hχ
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  refine ⟨?_, ?_⟩
  · have : (E χ 1 : ℤ) + E χ (-1) = R χ 1 + R χ 3 := by exact_mod_cast e1
    rw [this] at h0; exact h0
  · have : (E χ gi : ℤ) + E χ (-gi) = R χ 0 + R χ 2 := by exact_mod_cast e2
    rw [this] at h1
    refine h1.trans ?_
    rw [Int.modEq_iff_dvd]
    have hs' : (R χ 0 : ℤ) + R χ 2 = Q p - (R χ 1 + R χ 3) := by
      have : (R χ 0 + R χ 1 + R χ 2 + R χ 3 : ℤ) = Q p := by exact_mod_cast hs
      linarith
    obtain ⟨k, hk⟩ := hQ
    refine ⟨-(k : ℤ) + (R χ 1 + R χ 3), ?_⟩
    rw [hs']; push_cast [hk]; ring
end QuarterSumLadder
