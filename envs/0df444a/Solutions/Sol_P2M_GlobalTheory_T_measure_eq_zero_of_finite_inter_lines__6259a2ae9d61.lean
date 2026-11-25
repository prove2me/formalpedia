-- Prove2me | solution 1 for P2M_GlobalTheory_T_measure_eq_zero_of_finite_inter_lines__6259a2ae9d61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:12.798925+00:00
-- url     : https://prove2.me/submissions/1e18dcdc-383f-490b-b3a9-b54a86faca3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureEqZeroOfFiniteInterLines
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureEqZeroOfFiniteInterLinesStatement
import Theorems.Thm_GlobalTheory_measure_eq_zero_of_finite_inter_lines


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V), MeasurableSet Z → ∀ y : V, (∀ x : V, {t : K | x + t • y ∈ Z}.Finite) → μ Z = 0 := by
  first | exact @GlobalTheory.measure_eq_zero_of_finite_inter_lines | exact GlobalTheory.measure_eq_zero_of_finite_inter_lines | (intros; apply GlobalTheory.measure_eq_zero_of_finite_inter_lines <;> assumption)
end _root_.GlobalTheory.T
