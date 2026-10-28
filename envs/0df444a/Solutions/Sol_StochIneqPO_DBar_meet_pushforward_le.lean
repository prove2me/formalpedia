-- Prove2me | solution 1 for StochIneqPO.DBar.meet_pushforward_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:24:08.470027+00:00
-- url     : https://prove2.me/submissions/e67a6996-2a89-46d5-b2c2-55e1def2996a

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
import Definitions.Def_StochIneqPO_DBar_meetPath

open MeasureTheory

namespace Aux_SIPO_meet

open StochIneqPO.DBar

lemma meas_meet : Measurable meetPath := by
  unfold meetPath
  exact measurable_pi_lambda _ (fun n =>
    ((measurable_pi_apply n).comp measurable_fst).min ((measurable_pi_apply n).comp measurable_snd))

lemma meas_shift : Measurable (shift (E := ℝ)) := by
  unfold shift
  exact measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1))

lemma stochLE_of (ν : Measure ((ℤ → ℝ) × (ℤ → ℝ))) [IsProbabilityMeasure ν]
    (π : (ℤ → ℝ) × (ℤ → ℝ) → (ℤ → ℝ)) (hπ : Measurable π) (hle : ∀ z, meetPath z ≤ π z) :
    StochIneqPO.Comparison.StochLE (ν.map meetPath) (ν.map π) := by
  intro f hf hmono ⟨C, hC⟩
  rw [integral_map meas_meet.aemeasurable hf.aestronglyMeasurable,
    integral_map hπ.aemeasurable hf.aestronglyMeasurable]
  apply integral_mono
  · exact Integrable.of_bound (hf.comp meas_meet).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hC _))
  · exact Integrable.of_bound (hf.comp hπ).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hC _))
  · intro z
    exact hmono (hle z)

end Aux_SIPO_meet

open StochIneqPO.DBar Aux_SIPO_meet in
theorem solution
    (P Q : Measure (ℤ → ℝ))
    (ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)))
    (hν : IsPairShiftInvariant ν)
    (hνP : ν.map Prod.fst = P) (hνQ : ν.map Prod.snd = Q) :
    IsShiftInvariant (ν.map meetPath) ∧
      StochIneqPO.Comparison.StochLE (ν.map meetPath) P ∧ StochIneqPO.Comparison.StochLE (ν.map meetPath) Q := by
  obtain ⟨hprob, hinv⟩ := hν
  refine ⟨⟨Measure.isProbabilityMeasure_map meas_meet.aemeasurable, ?_⟩, ?_, ?_⟩
  · have hcomm : shift ∘ meetPath = meetPath ∘ Prod.map (shift (E := ℝ)) (shift (E := ℝ)) := by
      funext z n
      rfl
    have hpm : Measurable (Prod.map (shift (E := ℝ)) (shift (E := ℝ))) :=
      meas_shift.prodMap meas_shift
    rw [Measure.map_map meas_shift meas_meet, hcomm, ← Measure.map_map meas_meet hpm, hinv]
  · rw [← hνP]
    exact stochLE_of ν Prod.fst measurable_fst (fun z n => min_le_left _ _)
  · rw [← hνQ]
    exact stochLE_of ν Prod.snd measurable_snd (fun z n => min_le_right _ _)
