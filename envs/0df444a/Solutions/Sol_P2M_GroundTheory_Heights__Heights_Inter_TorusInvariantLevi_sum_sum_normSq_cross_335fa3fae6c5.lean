-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:41.642728+00:00
-- url     : https://prove2.me/submissions/cdace26e-ccc9-4aa8-abfb-bb61a73ff000

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution (z w : J → ℂ) :
    ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 =
      2 * (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) := by
  set B : J → ℝ := fun j => (z j).re * (w j).re + (z j).im * (w j).im with hB
  set D : J → ℝ := fun j => (z j).re * (w j).im - (z j).im * (w j).re with hD
  have hterm : ∀ j l, ‖z j * w l - z l * w j‖ ^ 2 =
      ‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ‖z l‖ ^ 2 * ‖w j‖ ^ 2 - 2 * (B j * B l + D j * D l) := by
    intro j l
    simp only [hB, hD, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have e1 : sqSum z * sqSum w = ∑ j, ∑ l, ‖z j‖ ^ 2 * ‖w l‖ ^ 2 := by
    rw [sqSum, sqSum, Finset.sum_mul_sum]
  have e2 : sqSum z * sqSum w = ∑ j, ∑ l, ‖z l‖ ^ 2 * ‖w j‖ ^ 2 := by
    rw [mul_comm, sqSum, sqSum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
  have e3 : reInner z w ^ 2 = ∑ j, ∑ l, B j * B l := by
    rw [reInner_apply, sq, Finset.sum_mul_sum]
  have e4 : reInner z (Complex.I • w) ^ 2 = ∑ j, ∑ l, D j * D l := by
    rw [reInner_apply, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hD, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hsplit : ∑ j, ∑ l, (‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ‖z l‖ ^ 2 * ‖w j‖ ^ 2 - 2 * (B j * B l + D j * D l)) =
      ∑ j, ∑ l, ‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ∑ j, ∑ l, ‖z l‖ ^ 2 * ‖w j‖ ^ 2 -
        2 * (∑ j, ∑ l, B j * B l + ∑ j, ∑ l, D j * D l) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hterm j l, hsplit, ← e1, ← e2,
    ← e3, ← e4]
  ring
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
