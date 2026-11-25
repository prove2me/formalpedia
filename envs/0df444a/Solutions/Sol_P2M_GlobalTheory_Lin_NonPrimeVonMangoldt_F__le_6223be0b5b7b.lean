-- Prove2me | solution 1 for P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:45.049508+00:00
-- url     : https://prove2.me/submissions/f44c05e7-9759-4fdd-ac20-f2bf6635bc9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
theorem _root_.solution (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) ≤ 4 * (((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ) * ((2 : ℝ) ^ (-(3 / 4) : ℝ)) ^ k) := by
  rw [F₂_eq]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.ofNat_le_cast.mpr p.prop.two_le
  set x : ℝ := ((p : ℕ) : ℝ) with hx
  have h1 : Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hp.le (by norm_num)
  have h3 : x ^ (-(3 / 4) : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)
  calc Real.log x / (x ^ (k + 2)) ^ (3 / 4 : ℝ)
      ≤ (x ^ (1 / 4 : ℝ) / (1 / 4)) / (x ^ (k + 2)) ^ (3 / 4 : ℝ) := by gcongr
    _ = 4 * (x ^ (-(5 / 4) : ℝ) * (x ^ (-(3 / 4) : ℝ)) ^ k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
          ← Real.rpow_mul hp.le, ← Real.rpow_add hp, div_div, mul_comm (1 / 4 : ℝ), ← div_div,
          ← Real.rpow_sub hp]
        have : (1 / 4 : ℝ) - ((k + 2 : ℕ) : ℝ) * (3 / 4) = -(5 / 4) + -(3 / 4) * (k : ℝ) := by
          push_cast; ring
        rw [this]; ring
    _ ≤ _ := by gcongr
end GlobalTheory.Lin.NonPrimeVonMangoldt
