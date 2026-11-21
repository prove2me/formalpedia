-- Prove2me | solution 1 for OnlineBeckFiala.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:12.094915+00:00
-- url     : https://prove2.me/submissions/b7443edb-f865-4014-9328-af8f77ec25b6

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

section
open MeasureTheory

namespace OnlineBeckFiala

namespace Dev.Eq10

lemma nullMeas (u : ℝ → ℝ) (hu : IntegrableOn (fun y => Real.exp (-u y)) (Set.Ioo (-1) 1))
    (r : ℝ) :
    NullMeasurableSet {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ r < u y} volume := by
  have hf : AEMeasurable (fun y => Real.exp (-u y)) (volume.restrict (Set.Ioo (-1) 1)) :=
    hu.aemeasurable
  have h1 := hf.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at h1
  have hT' : MeasurableSet {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ hf.mk _ y < Real.exp (-r)} :=
    measurableSet_Ioo.inter (measurableSet_lt hf.measurable_mk measurable_const)
  refine hT'.nullMeasurableSet.congr ?_
  refine Filter.eventuallyEq_set.mpr (h1.mono fun y hy => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hI, hlt⟩
    refine ⟨hI, ?_⟩
    rw [← hy hI] at hlt
    have := Real.exp_lt_exp.mp hlt
    linarith
  · rintro ⟨hI, hlt⟩
    refine ⟨hI, ?_⟩
    rw [← hy hI]
    exact Real.exp_lt_exp.mpr (by linarith)

end Dev.Eq10

theorem chk_eq_10 (u : ℝ → ℝ) (hu : IntegrableOn (fun y => Real.exp (-u y)) (Set.Ioo (-1) 1))
    (r : ℝ) :
    potLaw u {y | r < u y} =
        ENNReal.ofReal ((Zu u)⁻¹ * ∫ y in {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ r < u y}, Real.exp (-u y)) ∧
      potLaw u {y | r < u y} ≤ ENNReal.ofReal (2 / Zu u * Real.exp (-r)) := by
  set T : Set ℝ := {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ r < u y} with hTdef
  have hTsub : T ⊆ Set.Ioo (-1) 1 := fun y hy => hy.1
  have hTi : IntegrableOn (fun y => Real.exp (-u y)) T := hu.mono_set hTsub
  have hZ : 0 ≤ Zu u := integral_nonneg fun y => (Real.exp_pos _).le
  have hnm : NullMeasurableSet T volume := Dev.Eq10.nullMeas u hu r
  have key : potLaw u {y | r < u y} =
      ENNReal.ofReal (Zu u)⁻¹ * ∫⁻ y in T, ENNReal.ofReal (Real.exp (-u y)) := by
    unfold potLaw
    rw [withDensity_apply']
    have : ∀ y, ENNReal.ofReal (uRho u 1 y) =
        (Set.Ioo (-1 : ℝ) 1).indicator
          (fun y => ENNReal.ofReal (Zu u)⁻¹ * ENNReal.ofReal (Real.exp (-u y))) y := by
      intro y
      unfold uRho
      by_cases hy : y ∈ Set.Ioo (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hy, ENNReal.ofReal_mul (inv_nonneg.mpr hZ)]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
  have hint : ENNReal.ofReal (∫ y in T, Real.exp (-u y)) =
      ∫⁻ y in T, ENNReal.ofReal (Real.exp (-u y)) :=
    ofReal_integral_eq_lintegral_ofReal hTi
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
  refine ⟨?_, ?_⟩
  · rw [key, ENNReal.ofReal_mul (inv_nonneg.mpr hZ), hint]
  · rw [key]
    have hle : ∫⁻ y in T, ENNReal.ofReal (Real.exp (-u y)) ≤
        ENNReal.ofReal (2 * Real.exp (-r)) := by
      calc ∫⁻ y in T, ENNReal.ofReal (Real.exp (-u y))
          ≤ ∫⁻ y in T, ENNReal.ofReal (Real.exp (-r)) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem₀ hnm] with y hy
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hy.2]))
        _ = ENNReal.ofReal (Real.exp (-r)) * volume T := by simp
        _ ≤ ENNReal.ofReal (Real.exp (-r)) * 2 := by
            gcongr
            calc volume T ≤ volume (Set.Ioo (-1 : ℝ) 1) := measure_mono hTsub
              _ = 2 := by simp [ENNReal.ofReal]; norm_num
        _ = ENNReal.ofReal (2 * Real.exp (-r)) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp [mul_comm]
    calc ENNReal.ofReal (Zu u)⁻¹ * ∫⁻ y in T, ENNReal.ofReal (Real.exp (-u y))
        ≤ ENNReal.ofReal (Zu u)⁻¹ * ENNReal.ofReal (2 * Real.exp (-r)) := by gcongr
      _ = ENNReal.ofReal (2 / Zu u * Real.exp (-r)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hZ)]
          congr 1; field_simp

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_eq_10 := @OnlineBeckFiala.chk_eq_10
