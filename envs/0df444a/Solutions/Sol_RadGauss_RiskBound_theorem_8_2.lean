-- Prove2me | solution 2 for RadGauss.RiskBound.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:09.136021+00:00
-- url     : https://prove2.me/submissions/04af8a1c-fb95-42bd-bc76-e0d67d1fdf71

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp
import Theorems.Thm_RadGauss_RiskBound_combined_bound
import Theorems.Thm_RadGauss_RiskBound_symmetrization

set_option autoImplicit false
open MeasureTheory
open RadGauss.RiskBound

-- carved from submission e1483903-396e-4d6b-a71d-075cee0a7dd6, lines 726-766

theorem solution {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P) ≤
          ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
            rademacherComplexity P n (phiTildeComp φ F) +
            ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)))}
      ≤ ENNReal.ofReal δ := by
  have hsym := RadGauss.RiskBound.symmetrization φ hφ hφ01 F hF P n hn hsup hrad hdbl
  refine le_trans (measure_mono ?_) (RadGauss.RiskBound.combined_bound L φ hL hφ hL01 hφ01 hdom F hF P n hn δ hδ0 hδ1 hsup)
  rintro S ⟨f, hf, hne⟩
  refine ⟨f, hf, fun hle => hne ?_⟩
  calc ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P)
      ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (8 * Real.log (2 / δ) / n)) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P))) +
          ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
          ENNReal.ofReal (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
          ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)) := by
        gcongr; exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr
