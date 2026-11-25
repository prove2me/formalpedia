-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__div_rpow_le_inv_pow_11dc30a365ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:59.701973+00:00
-- url     : https://prove2.me/submissions/bbeaadb7-8db1-428a-83b4-36801d6593dc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {k r : ℕ} {C δ : ℝ} (hk : 1 ≤ k) (hC : 1 ≤ C) (hδ : δ ≤ 1 / 4) (hCk : C ^ 3 ≤ k) :
    (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ ((k : ℝ) ^ r)⁻¹ := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hkne : (k:ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hb0 : 0 < C / k := div_pos hC0 hk0
  have hCk' : C ≤ k := by
    nlinarith [mul_nonneg (mul_nonneg hC0.le (sub_nonneg.2 hC)) (by linarith : (0:ℝ) ≤ C + 1)]
  have hb1 : C / k ≤ 1 := by rw [div_le_iff₀ hk0]; linarith
  have he : (3:ℝ) * ((r:ℝ) / 2) ≤ 2 * (r : ℝ) * (1 - δ) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.2 hδ)]
  have hb3 : (C / k) ^ 3 ≤ ((k:ℝ) ^ 2)⁻¹ := by
    rw [div_pow, div_le_iff₀ (pow_pos hk0 3)]
    calc C ^ 3 ≤ k := hCk
      _ = ((k:ℝ) ^ 2)⁻¹ * (k:ℝ) ^ 3 := by
        rw [eq_comm, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hkne)]; ring
  have hkr : (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) = ((k:ℝ) ^ r)⁻¹ := by
    rw [Real.inv_rpow (pow_nonneg hk0.le 2)]
    congr 1
    rw [← Real.rpow_natCast (k:ℝ) 2, ← Real.rpow_mul hk0.le, ← Real.rpow_natCast (k:ℝ) r]
    congr 1; push_cast; ring
  calc (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ (C / k) ^ ((3:ℝ) * ((r:ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hb0 hb1 he
    _ = ((C / k) ^ 3) ^ ((r:ℝ) / 2) := by
        rw [Real.rpow_mul hb0.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ ≤ (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) :=
        Real.rpow_le_rpow (pow_nonneg hb0.le 3) hb3 (by positivity)
    _ = ((k:ℝ) ^ r)⁻¹ := hkr
end Formalism.MainNotions.BridgeLemma₂
