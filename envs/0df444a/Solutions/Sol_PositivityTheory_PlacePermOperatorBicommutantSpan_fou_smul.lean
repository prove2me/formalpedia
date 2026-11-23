-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.fou_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:53.071054+00:00
-- url     : https://prove2.me/submissions/06f4c3aa-ce4e-4c4a-b04e-cae956ce852f

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
omit h
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
end PositivityTheory.PlacePermOperatorBicommutantSpan
