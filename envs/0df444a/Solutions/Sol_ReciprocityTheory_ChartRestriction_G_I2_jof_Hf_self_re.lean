-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.jof_Hf_self_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:36.945794+00:00
-- url     : https://prove2.me/submissions/41b5f0f7-64db-4ac7-93c4-61bc7d145878

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq x, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Hf, Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
  | rw [← Complex.ofReal_pow, Complex.ofReal_re]
  | norm_cast
  | simp [sq]
end ReciprocityTheory.ChartRestriction.G.I2
