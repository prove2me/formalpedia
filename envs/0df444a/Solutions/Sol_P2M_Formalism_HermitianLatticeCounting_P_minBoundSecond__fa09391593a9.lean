-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_minBoundSecond__fa09391593a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:08.062513+00:00
-- url     : https://prove2.me/submissions/5f8ec75a-61cb-434f-953b-e9a561c27e0d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hyperbolicRatioSqLe
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minBoundSecondZero
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
theorem _root_.solution : MinII' := by
  intro k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hG hT hT' hg hv ht hDr hl'
    hdim hJop hJHS hAV hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg0 : 0 < g := by linarith
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hCTp : 0 < CT := lt_of_lt_of_le (div_pos hT' hT) hCT
  have heπ : 1 ≤ Real.exp 1 * Real.pi := by
    have := Real.add_one_le_exp 1
    have := Real.pi_gt_three
    nlinarith
  have hratio := hyperbolicRatioSqLe sh ch hsh hch hc
  rcases le_or_gt 1 sh with h1 | h1
  · have hz := minBoundSecondZero k r CT G T T' g v t loss JHS dim hr (by omega) hG hT hT' hg hv ht
      hlossp.le hdim hCT hkt hVF
    have h6 : ((1 + ch) / sh) ^ (2 * k) ≤ 6 ^ k := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (hratio.1 h1) k
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim) * ((1 + ch) / sh) ^ (2 * k) := by
          ring
      _ ≤ (loss * (CT / (k * g ^ (2 * r + 2))) ^ k) * 6 ^ k :=
          mul_le_mul hz h6 (by positivity) (by positivity)
      _ = loss * (6 * CT / (k * g ^ (2 * r + 2))) ^ k := by ring
      _ ≤ loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          apply mul_le_mul (le_mul_of_one_le_right hlossp.le (one_le_pow₀ hl')) _ (by positivity)
            (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
  · have h6 : (1 + ch) ^ 2 ≤ 6 := hratio.2 h1
    obtain ⟨q, hq⟩ : ∃ q, q = 1 + ch := ⟨_, rfl⟩
    rw [← hq] at h6 ⊢
    have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim (by omega) hC hG hT
      hg0 hv hDr hdim hJop hABS hrank
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have hDD : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k) = Dr ^ (2 * r + 4) := by
      have hone : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * s) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hDr.ne', one_pow]
      rw [hks, pow_add, ← mul_assoc, hone, one_mul]
    have hW : 0 ≤ (q / sh) ^ (2 * k) * T⁻¹ ^ k :=
      mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) (by positivity)
    have hT0 : T ≠ 0 := hT.ne'
    have hsh0 : sh ≠ 0 := hsh.ne'
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k:ℝ) ≠ 0 := hkR.ne'
    have hg00 : g ≠ 0 := hg0.ne'
    have hDr0 : Dr ≠ 0 := hDr.ne'
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := by
          ring
      _ ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
            (loss' ^ 2 * (C / (k * v)) ^ (2 * r * s) * Dr⁻¹ ^ (2 * s))) *
            ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := mul_le_mul_of_nonneg_right hmain hW
      _ = (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) := by
          have hTk : T ^ k * T⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT0, one_pow]
          have hsk : sh ^ (2 * k) * sh⁻¹ ^ (2 * k) = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hsh0, one_pow]
          rw [hGeq]
          linear_combination ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) * (sh ^ (2 * k) * sh⁻¹ ^ (2 * k))) * hTk +
            ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k))) * hsk
      _ ≤ (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * 1 * 6 ^ k *
            CT ^ k * loss := by
          rw [hDD]
          gcongr
          all_goals first | assumption | positivity | skip
      _ = loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          ring
end Formalism.HermitianLatticeCounting.P
