-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.pi_event_le_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:57.763294+00:00
-- url     : https://prove2.me/submissions/3a5ce9dc-f898-4754-a998-7795701904cb

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (μ : Fin 3 → Measure Space)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin 3)
    {E : Set (Fin 3 → Space)} (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hsections : ∀ q : Fin 2 → Space, μ i {p | i.insertNth (α := fun _ : Fin 3 => Space) p q ∈ E} ≤ C) :
    Measure.pi μ E ≤ C := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Space) i
  have hp := (measurePreserving_piFinSuccAbove μ i).symm e
  rw [← hp.measure_preimage hE.nullMeasurableSet, Measure.prod_apply_symm (e.symm.measurable hE)]
  calc
    _ ≤ ∫⁻ _ : Fin 2 → Space, C ∂Measure.pi (fun j => μ (i.succAbove j)) := by
      apply lintegral_mono
      intro q
      exact hsections q
    _ = C := by simp
end QEC.Coding.ProbabilisticConstruction.SphericalCap
