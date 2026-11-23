-- Prove2me | solution 1 for PI.PoincareSeriesInner.W.split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:24.106699+00:00
-- url     : https://prove2.me/submissions/900f51ae-e0e2-4611-a532-acadfc8ba68a

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
theorem _root_.solution (z : ℂ) : z = ∑ k, cf k * ((part k z).toReal : ℂ) := by
  simp only [Fin.sum_univ_four, cf, part]
  apply Complex.ext <;> simp [ENNReal.toReal_ofReal'] <;>
    linarith [max_zero_sub_max_neg_zero_eq_self z.re, max_zero_sub_max_neg_zero_eq_self z.im]
end PI.PoincareSeriesInner.W
