-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paMono_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:09.206744+00:00
-- url     : https://prove2.me/submissions/d303034a-3480-4e0b-ad3c-ff140e026f66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate

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
theorem _root_.solution (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : paMono α v = ∏ i, v i ^ α i := by
  simp [paMono, paPF, MvPolynomial.eval_monomial, Finsupp.prod_pow]
end ReciprocityTheory.ChartRestriction.G.I2.FPw
