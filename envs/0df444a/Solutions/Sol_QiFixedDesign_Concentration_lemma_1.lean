-- Prove2me | solution 1 for QiFixedDesign.Concentration.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:46:58.09028+00:00
-- url     : https://prove2.me/submissions/45943b01-9ed8-4bde-b34c-f91b08e6cba9

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_IntegralDifference
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist

open MeasureTheory Matrix Filter Topology
open scoped ENNReal
open QiFixedDesign.Concentration

noncomputable def geomMeasure : Measure ℝ :=
  Measure.sum (fun n : ℕ => ((1 / 2 : ℝ≥0∞) ^ (n + 1)) • Measure.dirac ((2 : ℝ) ^ (n + 1)))

instance : IsProbabilityMeasure geomMeasure := by
  refine ⟨?_⟩
  unfold geomMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h1 : (fun n : ℕ => (((1 / 2 : ℝ≥0∞) ^ (n + 1)) • Measure.dirac ((2 : ℝ) ^ (n + 1))) Set.univ) =
      fun n : ℕ => (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    ext n
    simp [pow_succ']
  rw [h1, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    nth_rw 1 [← ENNReal.inv_two_add_inv_two]
    exact ENNReal.add_sub_cancel_right (by norm_num)
  rw [hsub, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem solution : ¬ (∀ {Ξ : Type} [MetricSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ] (P Q : ProbabilityMeasure Ξ), (∀ f : Ξ → ℝ, LipschitzWith 1 f → IntegralDifferenceDefined (P : Measure Ξ) (Q : Measure Ξ) f) ∧ (WassersteinLinOpt.Ball.wassersteinDist 1 P Q : EReal) = ⨆ (f : Ξ → ℝ) (_ : LipschitzWith 1 f), signedIntegral (P : Measure Ξ) f - signedIntegral (Q : Measure Ξ) f) := by
  intro H
  let P0 : ProbabilityMeasure ℝ := ⟨geomMeasure, inferInstance⟩
  have hpos : positiveIntegral geomMeasure id = ⊤ := by
    unfold positiveIntegral geomMeasure
    rw [lintegral_sum_measure]
    have hterm : (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (id z) ∂(((1 / 2 : ℝ≥0∞) ^ (n + 1)) • Measure.dirac ((2 : ℝ) ^ (n + 1)))) =
        fun _ : ℕ => 1 := by
      ext n
      rw [lintegral_smul_measure, lintegral_dirac]
      dsimp
      rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← mul_pow, one_div,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    rw [hterm]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hneg : positiveIntegral geomMeasure (fun z => -id z) = 0 := by
    unfold positiveIntegral geomMeasure
    rw [lintegral_sum_measure]
    have hterm : (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (-id z) ∂(((1 / 2 : ℝ≥0∞) ^ (n + 1)) • Measure.dirac ((2 : ℝ) ^ (n + 1)))) =
        fun _ : ℕ => 0 := by
      ext n
      rw [lintegral_smul_measure, lintegral_dirac]
      dsimp
      have hle : -((2 : ℝ) ^ (n + 1)) ≤ 0 := neg_nonpos.mpr (by positivity)
      rw [ENNReal.ofReal_eq_zero.mpr hle, mul_zero]
    rw [hterm, tsum_zero]
  have hsigned : signedIntegral geomMeasure id = ⊤ := by
    unfold signedIntegral
    rw [hpos, hneg]
    rfl
  have hdef := (H P0 P0).1 id LipschitzWith.id
  exact hdef.2.2.1 ⟨hsigned, hsigned⟩
