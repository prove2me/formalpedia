-- Prove2me | solution 1 for PI.EF.PK.sidesBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:12.669985+00:00
-- url     : https://prove2.me/submissions/dff71166-1453-4659-b52e-aafb7da03129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_arsinh_le
import Theorems.Thm_PI_EF_PK_combine
import Theorems.Thm_PI_EF_PK_cLine_le_three
import Theorems.Thm_PI_EF_PK_rpow_cLine_le
import Theorems.Thm_PI_EF_PK_log_facts
import Theorems.Thm_PI_EF_PK_hor_side
import Theorems.Thm_PI_EF_PK_left_side
import Theorems.Thm_PI_EF_PK_vert_cancel
import Theorems.Thm_PI_EF_PK_sides_arith
import Theorems.Thm_PI_EF_PK_one_lt_cLine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution {κ C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hH : LogDerivHoriz κ C1)
    (hL : LogDerivLeft C2) : SidesBound κ (21 * C1 + 8 * C2) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'1 hgood
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hT'0 : 0 < T' := by linarith
  have hc1 : 1 < cLine u := one_lt_cLine hu2
  have hc3 : cLine u ≤ 3 := cLine_le_three hu2
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := log_facts hN hT hTu hTT' hT'1

  have hbot := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) (-T') (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (by rw [abs_neg, abs_of_pos hT'0])
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).2)
  have htop := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) T' (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (abs_of_pos hT'0)
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).1)
  have hleft := left_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u T'
    (C2 * Real.log (N * (T' + 2))) (by linarith) hT'0 (mul_nonneg hC2 hf6)
    (fun t ht => le_trans (hL N χ hχ t) (mul_le_mul_of_nonneg_left
      (Real.log_le_log (mul_pos (by linarith) (by positivity))
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith))) hC2))

  have hv := vert_cancel (fun t => logDeriv (DirichletCharacter.LFunction χ) ((cLine u : ℂ) + t * I))
    (fun t => (u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I)) T'
  unfold rectInt vertInt
  rw [hv]
  simp only [smul_eq_mul]
  refine le_trans (combine hbot htop hleft) ?_
  exact sides_arith hC1 hC2 (by linarith) (by linarith) hTu hTT' hc1 hc3
    (Real.rpow_nonneg (by linarith) _) (rpow_cLine_le hu2) hf1 hf2 hf3 hf4
    ((arsinh_le (2 * T') (by linarith)).trans hf5) (Real.arsinh_nonneg_iff.mpr (by linarith)) hf7
end PI.EF.PK
