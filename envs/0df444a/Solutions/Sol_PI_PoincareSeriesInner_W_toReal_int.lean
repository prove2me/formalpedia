-- Prove2me | solution 1 for PI.PoincareSeriesInner.W.toReal_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:45.935031+00:00
-- url     : https://prove2.me/submissions/c6e1c527-80d0-47f4-b95d-1a2b462744d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.PoincareSeriesInner PI.PoincareSeriesInner.W
universe u
namespace PI.PoincareSeriesInner.W
theorem _root_.solution {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hfin : ∫⁻ x, f x ∂ν ≠ ⊤) (hpt : ∀ x, f x ≠ ⊤) :
    Integrable (fun x => ((f x).toReal : ℂ)) ν ∧
      ∫ x, ((f x).toReal : ℂ) ∂ν = (((∫⁻ x, f x ∂ν).toReal : ℝ) : ℂ) := by
  refine ⟨(integrable_toReal_of_lintegral_ne_top hf hfin).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_toReal hf (Filter.Eventually.of_forall fun x => (hpt x).lt_top)]
end PI.PoincareSeriesInner.W
