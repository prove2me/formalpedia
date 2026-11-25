-- Prove2me | solution 1 for PI.GTNum.abs_cBr_le_cBd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:49.16546+00:00
-- url     : https://prove2.me/submissions/8c86d74f-26d0-4339-802d-0b39f9d91b91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
import Theorems.Thm_PI_GTNum_abs_cBr_le_top
import Theorems.Thm_PI_GTNum_interlacing_defect_eq_card
import Theorems.Thm_PI_GTNum_lam_le_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
namespace PI.GTNum
theorem _root_.solution (hI : Interlace h lam sg) :
    |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg := by
  set K : ℕ := ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card with hK
  have hD1 : (N : ℤ) * D1 h lam sg = ((N * K : ℕ) : ℤ) := by
    rw [interlacing_defect_eq_card h lam sg hI, ← hK, Nat.cast_mul]
  have hN : 0 < N := by omega
  have hsp : lam.spread = lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + N := by
    unfold DomWeight.spread
    rw [dif_pos hN]
  have hlast := lam_le_last h lam 0 (by omega)
  have hb := abs_cBr_le_top h lam sg hI
  rw [← hK] at hb
  have hb2 : (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K) ≤
      (2 * lam.spread) ^ (N * K) := by
    calc (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K)
        ≤ (2 * lam.spread) ^ (n * K) := by
          apply pow_le_pow_left₀ (by omega)
          rw [hsp]
          omega
      _ ≤ (2 * lam.spread) ^ (N * K) := by
          apply pow_le_pow_right₀ (by rw [hsp]; omega)
          exact Nat.mul_le_mul_right K (by omega)
  unfold cBd
  rw [hD1, Int.cast_natCast, Real.rpow_natCast, ← Int.cast_abs]
  exact_mod_cast le_trans hb hb2
end PI.GTNum
