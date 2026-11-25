-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:11.351806+00:00
-- url     : https://prove2.me/submissions/6f9bfaa7-4c4d-4d79-aa29-babfe4e6c205

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartsOfRegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_apply_faf90b8a71c2
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution (D : ℕ) {c : ℝ} (hc : 0 < c) :
    scaleHom D hc ⁻¹' ball 0 c ⊆ ball 0 1 := by
  intro z hz
  have hz' : ‖(c : ℂ) • z‖ < c := by simpa [scaleHom_apply] using hz
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hz'
  simpa using (mul_lt_iff_lt_one_right hc).1 hz'
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
