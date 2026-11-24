-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_minBoundFirst__4de30799fb86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:07.971583+00:00
-- url     : https://prove2.me/submissions/2e747af8-39dd-4f6f-82cb-39f2aec309ae

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gainBase_pow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volumeFactor_mul_sq_div_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinI' := by
  intro k r C G T g v t Dr loss loss' JHS Jop dim hk hC hG hT hg hv ht hDr hl' hdim hJop hJHS
    hAV hloss hVF hABS hrank
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim hk1 hC hG hT hg hv
    hDr hdim hJop hABS hrank
  rcases le_total 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (G / (T * Dr ^ 2)) t g) with h | h
  · rw [min_eq_left h, one_pow, mul_one]
    calc _ ≤ loss * t⁻¹ ^ k := hVF
      _ = loss * 1 * t⁻¹ ^ k := by ring
      _ ≤ loss * loss' ^ 2 * t⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_pow₀ hl') hlossp.le)
            (by positivity)
  · rw [min_eq_right h, gainBase_pow k r C (G / (T * Dr ^ 2)) t g hk1 hC]
    have eG : (G / (T * Dr ^ 2)) ^ k = (G / T) ^ k * Dr⁻¹ ^ (2 * k) := by
      rw [pow_mul Dr⁻¹ 2 k, ← mul_pow]; congr 1; ring
    have et : t⁻¹ ^ k * t ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ ht.ne', one_pow]
    rw [eG]
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have eCv : (C / (k * v)) ^ (2 * r * s) = (C / k) ^ (2 * r * s) * v⁻¹ ^ (2 * r * s) := by
      rw [← mul_pow]; congr 1; ring
    have hone : Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * r + 4) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hDr.ne', one_pow]
    have eDi : Dr⁻¹ ^ (2 * s) = Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * k) := by
      rw [hks, pow_add]
      linear_combination (-(Dr⁻¹ ^ (2 * s))) * hone
    have hZ : 0 ≤ (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
        Dr⁻¹ ^ (2 * k) := by positivity
    have hAVD : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4) ≤
        loss := by
      calc _ ≤ 1 * Dr ^ (2 * r + 4) := mul_le_mul_of_nonneg_right hAV (by positivity)
        _ ≤ loss := by rw [one_mul]; exact hloss
    calc _ ≤ _ := hmain
      _ = ((Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4)) *
          ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := by rw [eCv, eDi]; ring
      _ ≤ loss * ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := mul_le_mul_of_nonneg_right hAVD hZ
      _ = loss * loss' ^ 2 * t⁻¹ ^ k * ((G / T) ^ k * Dr⁻¹ ^ (2 * k) * t ^ k *
            (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * s)) := by
          linear_combination (-(loss * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (C / k) ^ (2 * r * s) * Dr⁻¹ ^ (2 * k))) * et
end Formalism.HermitianLatticeCounting.P
