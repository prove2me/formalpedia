-- Prove2me | solution 1 for PI.PoincareSeriesInner.W.part_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:44.929824+00:00
-- url     : https://prove2.me/submissions/273ba732-283b-4f93-a0b9-510950f4def7

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
theorem _root_.solution (k : Fin 4) (z : ℂ) : part k z ≤ ‖z‖ₑ := by
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  fin_cases k
  · simpa using Complex.re_le_norm z
  · simpa using le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z)
  · simpa using Complex.im_le_norm z
  · simpa using le_trans (neg_le_abs z.im) (Complex.abs_im_le_norm z)
end PI.PoincareSeriesInner.W
