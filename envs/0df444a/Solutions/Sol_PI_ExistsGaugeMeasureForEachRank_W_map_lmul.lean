-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.map_lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:31.606797+00:00
-- url     : https://prove2.me/submissions/e6ef25e2-048f-4aba-9ec2-824cac10c9d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_toCircle_coe
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_continuous_Gm
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_continuous_lmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Gm_add
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conj_mul_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_mem_UWb_iff


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
theorem _root_.solution (s : Mat 0 r) (hs : s ∈ UWb 0 r) : (μG r).map (lmulM s) = μG r := by
  obtain ⟨u, hu, rfl⟩ := (mem_UWb_iff s).1 hs
  rw [conj_mul_iff] at hu
  have hα : ((AddCircle.toCircle ((Complex.arg u : ℝ) : AddCircle (2 * π)) : Circle) : ℂ) = u := by
    rw [toCircle_coe]
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hu] at this
    simpa using this
  unfold μG
  rw [Measure.map_map (continuous_lmulM _).measurable continuous_Gm.measurable]
  have hcomp : lmulM (dgl r u) ∘ Gm r =
      Gm r ∘ (fun θ => ((Complex.arg u : ℝ) : AddCircle (2 * π)) + θ) := by
    funext θ
    simp only [Function.comp_apply]
    rw [Gm_add, hα]
  rw [hcomp, ← Measure.map_map continuous_Gm.measurable (measurable_const_add _),
    map_add_left_eq_self]
end PI.ExistsGaugeMeasureForEachRank.W
