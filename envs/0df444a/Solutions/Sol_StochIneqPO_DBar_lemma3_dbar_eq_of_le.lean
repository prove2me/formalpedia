-- Prove2me | solution 1 for StochIneqPO.DBar.lemma3_dbar_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:30:11.170433+00:00
-- url     : https://prove2.me/submissions/d016fbf0-29e8-4ec9-ac1c-1d8c2bb2db32

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar
import Theorems.Thm_StochIneqPO_DBar_theorem7_stationary_coupling
import Theorems.Thm_StochIneqPO_DBar_lemma2_dbar_ge

open MeasureTheory StochIneqPO.DBar

theorem solution
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q)
    (hPQ : StochIneqPO.Comparison.StochLE P Q) :
    dbar P Q = (∫ ω, ω 0 ∂Q) - (∫ ω, ω 0 ∂P) := by
  have hge := lemma2_dbar_ge P Q hP hQ hPi hQi
  obtain ⟨ν, hν, hν1, hν2, hle⟩ := theorem7_stationary_coupling P Q hP hQ hPQ
  have h0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
  have hI1 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.1 0) ν := by
    rw [← hν1] at hPi
    exact (integrable_map_measure h0.aestronglyMeasurable measurable_fst.aemeasurable).mp hPi
  have hI2 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0) ν := by
    rw [← hν2] at hQi
    exact (integrable_map_measure h0.aestronglyMeasurable measurable_snd.aemeasurable).mp hQi
  have hEP : ∫ ω, ω 0 ∂P = ∫ z, z.1 0 ∂ν := by
    rw [← hν1, integral_map measurable_fst.aemeasurable h0.aestronglyMeasurable]
  have hEQ : ∫ ω, ω 0 ∂Q = ∫ z, z.2 0 ∂ν := by
    rw [← hν2, integral_map measurable_snd.aemeasurable h0.aestronglyMeasurable]
  have hcost : ∫ z, |z.1 0 - z.2 0| ∂ν = (∫ ω, ω 0 ∂Q) - (∫ ω, ω 0 ∂P) := by
    rw [hEP, hEQ, ← integral_sub hI2 hI1]
    refine integral_congr_ae ?_
    filter_upwards [hle] with z hz
    rw [abs_of_nonpos (by linarith [hz 0])]; ring
  have hle' : dbar P Q ≤ (∫ ω, ω 0 ∂Q) - (∫ ω, ω 0 ∂P) := by
    unfold dbar
    refine csInf_le ⟨0, ?_⟩ ⟨ν, hν, hν1, hν2, hcost.symm⟩
    rintro c ⟨μ, -, -, -, rfl⟩
    exact integral_nonneg (fun z => abs_nonneg _)
  have := le_abs_self ((∫ ω, ω 0 ∂Q) - (∫ ω, ω 0 ∂P))
  rw [abs_sub_comm] at this
  linarith
