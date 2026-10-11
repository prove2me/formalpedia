-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.native_pairing_square_of_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:32:53.228883+00:00
-- url     : https://prove2.me/submissions/9cabcc8c-55b6-4917-b6a0-f2e3883e1d08

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_mixed_root_certificate
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_energy_of_enclosures
import Theorems.Thm_WeilDefect_RPB108_native_row_square_of_energy_floor
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem gram_scales_pos (i : Fin 3) : 0 < gramScales i := by
  fin_cases i <;> norm_num [gramScales, scales, Matrix.cons_val_two]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem native_dual_budget_identity :
    (∑ i : Fin 3, (nativeScaledEnvelope i)^2) = nativeDualSquare*retainedLower := by
  norm_num [nativeScaledEnvelope, nativePairingEnvelope, gramScales, scales, Matrix.cons_val_two,
    nativeDualSquare, retainedLower, Fin.sum_univ_succ]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem native_envelope_nonneg (i : Fin 3) : 0 ≤ nativePairingEnvelope i := by
  fin_cases i <;> norm_num [nativePairingEnvelope]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem native_pairing_endpoints (i : Fin 3) :
    -nativePairingEnvelope i ≤ nativePairingLower i ∧
    nativePairingUpper i ≤ nativePairingEnvelope i := by
  fin_cases i <;> norm_num [nativePairingEnvelope, nativePairingLower, nativePairingUpper]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem native_scaled_row_bound (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (i : Fin 3) : ‖((gramScales i*a i : ℝ) : ℂ)‖ ≤ nativeScaledEnvelope i := by
  have hab : |a i| ≤ nativePairingEnvelope i := abs_le.mpr
    ⟨(native_pairing_endpoints i).1.trans (ha i).1,
      (ha i).2.trans (native_pairing_endpoints i).2⟩
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (gram_scales_pos i), nativeScaledEnvelope]
  exact mul_le_mul_of_nonneg_left hab (gram_scales_pos i).le
end WeilDefect.RPB108.DNE27Even

theorem solution (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 4 → ℂ) :
    ‖nativePairing a z‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ) := by
  exact native_row_square_of_energy_floor
    (fun i => ((gramScales i*a i : ℝ) : ℂ)) (fun i => z i.succ)
    nativeScaledEnvelope retainedLower nativeDualSquare _
    (native_scaled_row_bound a ha) mixed_root_certificate.1
    native_dual_budget_identity.le (retained_energy_of_enclosures V hV z)
