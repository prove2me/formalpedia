-- Prove2me | solution 1 for PI.FglChordFactor.Wk.inhab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:28.907944+00:00
-- url     : https://prove2.me/submissions/2554d56c-21eb-437c-a824-d36dd1e62f8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Theorems.Thm_PI_FglChordFactor_Wk_wqc_isWq
import Theorems.Thm_PI_FglChordFactor_Wk_norm_delta_Wc
import Theorems.Thm_PI_FglChordFactor_Wk_isWq_bridge
import Theorems.Thm_PI_FglChordFactor_Wk_flog_bridge
import Theorems.Thm_PI_AddIntG_Wk_coeff_one_flog
import Theorems.Thm_PI_AddIntG_Wk_flog_constantCoeff
import Theorems.Thm_additive_integral_generation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
namespace PI.FglChordFactor.Wk
theorem _root_.solution : ∃ (W : WeierstrassCurve ℂ_[2]) (wq ex : PowerSeries ℂ_[2]),
    IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1 ∧
    IsWq W wq ∧ PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex (flog W wq) = PowerSeries.X ∧
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[2]) := by
  have hW := wqc_isWq
  have hl0 : PowerSeries.constantCoeff (flog Wc wqc) = 0 := PI.AddIntG.Wk.flog_constantCoeff Wc wqc
  have hu : IsUnit (PowerSeries.coeff 1 (flog Wc wqc)) := by
    rw [flog_bridge, PI.AddIntG.Wk.coeff_one_flog (isWq_bridge hW)]; exact isUnit_one
  set ex := PowerSeries.substInvOfIsUnit (flog Wc wqc) hu
  have hex0 : PowerSeries.constantCoeff ex = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ hu
  have hex : PowerSeries.subst ex (flog Wc wqc) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right (flog Wc wqc) hl0 hu
  have hI := (additive_integral_generation 2 Wc wqc ex (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc])
    (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc])
    (isWq_bridge hW) hex0 hex).1
  exact ⟨Wc, wqc, ex, by simp [IsIntP, Wc], by simp [IsIntP, Wc], by simp [IsIntP, Wc], by simp [IsIntP, Wc],
    by simp [IsIntP, Wc], norm_delta_Wc, hW, hex0, hex, hI⟩
end PI.FglChordFactor.Wk
