-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:09.301678+00:00
-- url     : https://prove2.me/submissions/9b69d5b3-5646-474e-ba65-7c0ae5231339

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
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
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)
local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution (R : RegChartDataA A) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (z : Fin D → ℂ) (ht : 0 < t) (hK : ∀ y ∈ ball z t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.smoothed ρ K t j z = molli ρ t (R.u j) z := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.smoothed molli
  have hae : ∀ᵐ w : Fin D → ℂ, ∀ i ∈ R.S j, w i ≠ z i := by
    rw [Filter.eventually_all_finset]
    intro i _
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton (z i))
  refine integral_congr_ae (hae.mono fun w hw => ?_)
  by_cases hρ : ρ.scaled t w = 0
  · simp [hρ]
  have hw1 : ‖w‖ < t := by
    have hs : t⁻¹ • w ∈ ball (0 : Fin D → ℂ) 1 :=
      ρ.support_subset fun h0 => hρ (by simp [Mollifier.scaled, h0])
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hs
    rwa [inv_mul_lt_iff₀ ht, mul_one] at hs
  have hb : z - w ∈ ball z t := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hw1
  have hd : z - w ∉ coordDiv (R.S j) := by
    rintro ⟨i, hi, h0⟩
    exact hw i hi (by rw [Pi.sub_apply, sub_eq_zero] at h0; exact h0.symm)
  simp only [GroundTheory.Heights₂.Heights.Regular.RegChartData.trunc, limsupExt, if_neg hd]
  rw [max_eq_left (hK _ hb hd)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
