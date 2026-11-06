-- Prove2me | solution 1 for ProbabilityTheory.integrable_prmPieceLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:12:15.529416+00:00
-- url     : https://prove2.me/submissions/9340455b-191e-4408-9caa-4c4051ac78d4

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {E : Type*} [MeasurableSpace E] {m : Measure E}
    [SigmaFinite m] {k : ℕ} [Nonempty E]
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) :
    Integrable g (prmPieceLaw m k) := by
  have htop : m (prmPiece m k) ≠ ⊤ :=
    (lt_of_le_of_lt
      (measure_mono (disjointed_subset (spanningSets m) k))
      (measure_spanningSets_lt_top m k)).ne
  unfold prmPieceLaw
  split_ifs with h
  · exact integrable_dirac' hg.stronglyMeasurable (by finiteness)
  · exact (integrable_smul_measure
      (ENNReal.inv_ne_zero.2 htop)
      (ENNReal.inv_ne_top.2 h)).mpr hgi
