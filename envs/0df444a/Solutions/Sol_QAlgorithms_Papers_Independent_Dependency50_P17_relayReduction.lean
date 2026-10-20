-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P17.relayReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:09.066006+00:00
-- url     : https://prove2.me/submissions/b615e3ee-0fbc-45be-b61f-47349b812940

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.3,5, Section II.C.1: compute-and-forward message exchange.
Alice subtracts her own message from her received sum, and Bob does likewise.
The bound includes uplink error and both downlink errors, so sufficient downlink
reliability is explicit. It applies to every COMP code and every block length. -/
theorem solution {F Omega : Type*} [Field F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] [MeasurableSpace Omega]
    {ell : ℕ} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (a b u da db : Omega → (Fin ell → F))
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u)
    (hda : Measurable da) (hdb : Measurable db)
    (hmsg : UniformMessagePair mu a b) :
    (∀ w, u w = a w + b w → da w = u w → db w = u w →
      da w - a w = b w ∧ db w - b w = a w) ∧
    mu {w | da w - a w ≠ b w ∨ db w - b w ≠ a w} ≤
      mu {w | u w ≠ a w + b w} + mu {w | da w ≠ u w} + mu {w | db w ≠ u w}
    := by
  refine ⟨fun w h1 h2 h3 => ?_, ?_⟩
  · rw [h2, h1]; rw [h3, h1]; exact ⟨add_sub_cancel_left _ _, add_sub_cancel_right _ _⟩
  · calc mu {w | da w - a w ≠ b w ∨ db w - b w ≠ a w}
        ≤ mu ({w | u w ≠ a w + b w} ∪ {w | da w ≠ u w} ∪ {w | db w ≠ u w}) := by
          apply measure_mono
          intro w hw
          by_contra hc
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
          obtain ⟨⟨h1, h2⟩, h3⟩ := hc
          simp only [Set.mem_ofPred_eq, h2, h3, h1, add_sub_cancel_left, add_sub_cancel_right,
            ne_eq, not_true_eq_false, or_self] at hw
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)


end

