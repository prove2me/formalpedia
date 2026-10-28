-- Prove2me | solution 1 for StochIneqPO.DBar.lemma2_dbar_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:26:46.295131+00:00
-- url     : https://prove2.me/submissions/3d325d9f-848a-4bfe-a3ec-f187e83adba7

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

open MeasureTheory

namespace Aux_SIPO_dbar

open StochIneqPO.DBar

lemma meas_shift : Measurable (shift (E := ℝ)) := by
  unfold shift
  exact measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1))

end Aux_SIPO_dbar

open StochIneqPO.DBar Aux_SIPO_dbar in
theorem solution
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    |(∫ ω, ω 0 ∂P) - (∫ ω, ω 0 ∂Q)| ≤ dbar P Q := by
  obtain ⟨hPp, hPs⟩ := hP
  obtain ⟨hQp, hQs⟩ := hQ
  unfold dbar
  apply le_csInf
  · refine ⟨_, P.prod Q, ⟨inferInstance, ?_⟩, ?_, ?_, rfl⟩
    · rw [← Measure.map_prod_map P Q meas_shift meas_shift, hPs, hQs]
    · simp
    · simp
  · rintro c ⟨ν, ⟨hνp, _⟩, hνP, hνQ, rfl⟩
    have he0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
    have hi1 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.1 0) ν := by
      rw [← hνP] at hPi
      exact (integrable_map_measure he0.aestronglyMeasurable
        measurable_fst.aemeasurable).mp hPi
    have hi2 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0) ν := by
      rw [← hνQ] at hQi
      exact (integrable_map_measure he0.aestronglyMeasurable
        measurable_snd.aemeasurable).mp hQi
    have h1 : ∫ ω, ω 0 ∂P = ∫ z, z.1 0 ∂ν := by
      rw [← hνP, integral_map measurable_fst.aemeasurable he0.aestronglyMeasurable]
    have h2 : ∫ ω, ω 0 ∂Q = ∫ z, z.2 0 ∂ν := by
      rw [← hνQ, integral_map measurable_snd.aemeasurable he0.aestronglyMeasurable]
    rw [h1, h2, ← integral_sub hi1 hi2]
    exact abs_integral_le_integral_abs
