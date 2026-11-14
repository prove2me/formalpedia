-- Prove2me | solution 1 for avram_chat24_count_nonneg_tsum_core
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T14:40:09.487726+00:00
-- url     : https://prove2.me/submissions/e9994f1e-4330-49ed-b0af-afc7d8b80574

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem solution
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (g : α → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg : Summable g) :
    Integrable g Measure.count ∧ (∫ x, g x ∂Measure.count) = ∑' x, g x := by
  have hnorm : Summable fun x => ‖g x‖ := by
    simpa [Real.norm_of_nonneg (hg0 _)] using hg
  have hint : Integrable g Measure.count := (integrable_count_iff (f := g)).mpr hnorm
  refine ⟨hint, ?_⟩
  have hnonneg : 0 ≤ᵐ[Measure.count] g := ae_of_all _ hg0
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hint.aestronglyMeasurable,
      lintegral_count (fun x => ENNReal.ofReal (g x)),
      ← ENNReal.ofReal_tsum_of_nonneg hg0 hg,
      ENNReal.toReal_ofReal (tsum_nonneg hg0)]
end
