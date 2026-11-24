-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:02.005813+00:00
-- url     : https://prove2.me/submissions/9d9c7024-97bd-4f9a-94c5-91ad36bb51c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (x y : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf x y) = Hf y x := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end ReciprocityTheory.ChartRestriction.G.I2.FPw
