-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_MollifiedLowerBound_proof_5068d8d26e40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:29.733637+00:00
-- url     : https://prove2.me/submissions/102e363d-96e1-40aa-8c15-e89803d435f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifierLowerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_kC
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_mem_ball_sub
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace MollifiedLowerBound
theorem _root_.solution (h0 : SubMeanPolydiscStatement)
    (h1 : PolyMaxLogConvexStatement) : MollifiedLowerBound.Statement := by
  intro D ρ b U u z t hU hu ht hzU hb
  set M2 := polyMax u z (2 * t)
  set M4 := polyMax u z (t / 4)
  obtain ⟨-, -, hatt, -⟩ := h1 D U u z (2 * t) hU hu (by positivity) hzU
  obtain ⟨x, hx, hux⟩ := hatt (t / 4) (by positivity) (by linarith)
  rw [mem_closedBall] at hx
  set B := closedBall x (3 / 2 * t) with hBdef
  have hBz : B ⊆ closedBall z (2 * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hzB : closedBall z t ⊆ B :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  obtain ⟨hint, hmean⟩ := h0 D U u x (3 / 2 * t) hU hu (by positivity) (hBz.trans hzU)
  rw [← hBdef] at hint hmean
  have hle2 : ∀ p ∈ B, u p ≤ M2 := fun p hp => le_polyMax hu.1 hzU (hBz hp)
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  have hV : volume.real B = (Real.pi * (3 / 2 * t) ^ 2) ^ D :=
    volume_real_closedBall_polydisc x (by positivity)
  have hVpos : 0 < volume.real B := by rw [hV]; positivity
  have hcint : IntegrableOn (fun _ => M2) B := integrableOn_const measure_closedBall_lt_top.ne

  have hIB : ∫ p in B, (M2 - u p) ≤ volume.real B * (M2 - M4) := by
    rw [integral_sub hcint hint, setIntegral_const, smul_eq_mul]
    rw [setAverage_eq, smul_eq_mul] at hmean
    have h := mul_le_mul_of_nonneg_left hmean hVpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul] at h
    rw [show M4 = u x from hux.symm]
    linarith

  set g : (Fin D → ℂ) → ℝ := B.indicator (fun p => M2 - u p) with hgdef
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q
    by_cases hq : q ∈ B
    · rw [hgdef, indicator_of_mem hq]; exact sub_nonneg.2 (hle2 q hq)
    · rw [hgdef, indicator_of_notMem hq]
  have hgint : Integrable g :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hcint.sub hint)
  have hBind : Integrable (B.indicator u) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hint
  set c : ℝ := (t ^ (2 * D))⁻¹ * b with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hsc : ∀ y, ρ.scaled t y ≤ c := fun y =>
    mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have key : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) ≤
      ∫ y, c * g (z - y) := by
    refine integral_mono (((integrable_scaled ρ ht).mul_const M2).sub
      (integrable_kC ρ ht hBind z)) ((hgint.comp_sub_left z).const_mul c) fun y => ?_
    by_cases hy : ρ.scaled t y = 0
    · simp only [hy, zero_mul, sub_zero]
      exact mul_nonneg hc0 (hg0 _)
    · have hm : z - y ∈ B := hzB (mem_ball_sub ρ ht hy z)
      simp only [hgdef, indicator_of_mem hm]
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_right (hsc y) (sub_nonneg.2 (hle2 _ hm))
  have hLHS : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) =
      M2 - molli ρ t u z := by
    rw [integral_sub ((integrable_scaled ρ ht).mul_const M2) (integrable_kC ρ ht hBind z),
      integral_mul_const, integral_scaled ρ ht, one_mul, molli_eq_C ρ ht hzB (φ := u)]
  have hRHS : ∫ y, c * g (z - y) = c * ∫ p in B, (M2 - u p) := by
    rw [integral_const_mul]
    congr 1
    have := (Measure.measurePreserving_sub_left volume z).integral_comp
      (Homeomorph.subLeft z).measurableEmbedding g
    rw [this, hgdef, integral_indicator measurableSet_closedBall]
  have hcV : c * volume.real B = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := by
    rw [hV, hcdef]
    have ht' : t ^ (2 * D) ≠ 0 := by positivity
    rw [mul_pow, ← pow_mul, mul_pow, pow_mul (3 / 2 : ℝ) 2 D]
    field_simp
  have hfin := mul_le_mul_of_nonneg_left hIB hc0
  have e : c * (volume.real B * (M2 - M4)) =
      Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (M2 - M4) := by
    rw [← hcV]; ring
  linarith
end MollifiedLowerBound
end GroundTheory.Heights₂.Heights.Regular
