-- Prove2me | solution 1 for PI.PoincareSeriesInner.W.measurable_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:34.490054+00:00
-- url     : https://prove2.me/submissions/6bae310d-2de8-49f2-9865-39b25e0d9cf4

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
theorem _root_.solution (k : Fin 4) : Measurable (part k) := by
  fin_cases k
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re.neg
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im.neg
end PI.PoincareSeriesInner.W
