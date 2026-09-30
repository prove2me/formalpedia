-- Prove2me | solution 1 for UnderstandingML.compression_bound_consistent
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:09:16.451716+00:00
-- url     : https://prove2.me/submissions/99d2790f-7d06-4b59-8327-f3a8559b5d98

import Theorems.Thm_UnderstandingML_compression_bound

open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) (hm0 : 0 < m) (B : (Fin k → Z) → Hyp)
    (hB : Measurable (fun p : (Fin k → Z) × Z ↦ loss (B p.1) p.2))
    (sel : (Fin m → Z) → Fin k → Fin m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | heldOutRisk loss sel S (compressedHyp B sel S) = 0 ∧
        8 * k * Real.log (m / δ) / m < risk loss D (compressedHyp B sel S)} ≤
      ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_)
    (compression_bound loss hloss D k m hk hm hm0 B hB sel δ hδ hδ1)
  rintro S ⟨h0, hlt⟩
  simp only [Set.mem_setOf_eq, h0, zero_mul, zero_div, Real.sqrt_zero, add_zero, zero_add]
  exact hlt
