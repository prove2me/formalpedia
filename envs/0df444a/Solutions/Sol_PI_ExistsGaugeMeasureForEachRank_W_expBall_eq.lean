-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.expBall_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:12.552961+00:00
-- url     : https://prove2.me/submissions/1acb1609-f10d-48d4-a179-305f031060eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_toCircle_coe
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_exp_dz
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_lieE_eq
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_norm_v0_eq_one
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_ofRealCoords_smul_centerCoord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (ρ : ℝ) :
    expBall (UWb 0 r) ρ = Gm r '' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x.1 ∈ Submodule.span ℝ {v0 r} := by
      rw [← lieE_eq]; exact x.2
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hx'
    have hn : ‖x.1‖ = |s| := by
      rw [← hs, norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs]
    have hlt : |s| < ρ := by
      rw [← hn]; exact mem_ball_zero_iff.1 hx
    refine ⟨(s : AddCircle (2 * π)), ⟨s, abs_lt.1 hlt, rfl⟩, ?_⟩
    show Gm r s = fun i j => NormedSpace.exp (unrealify x.1) i j
    rw [← hs, ofRealCoords_smul_centerCoord, exp_dz]
    unfold Gm
    rw [toCircle_coe]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hmem : s • v0 r ∈ lieE (UWb 0 r) := by
      rw [lieE_eq]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    refine ⟨⟨s • v0 r, hmem⟩, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      show ‖s • v0 r‖ < ρ
      rw [norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs, abs_lt]
      exact hs
    · show (fun i j => NormedSpace.exp (unrealify (s • v0 r)) i j) = Gm r s
      rw [ofRealCoords_smul_centerCoord, exp_dz]
      unfold Gm
      rw [toCircle_coe]
end PI.ExistsGaugeMeasureForEachRank.W
