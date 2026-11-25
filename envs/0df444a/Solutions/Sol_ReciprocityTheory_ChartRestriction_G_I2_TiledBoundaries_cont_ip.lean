-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.cont_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:16.122044+00:00
-- url     : https://prove2.me/submissions/fb7b172c-f489-4491-bab2-48a4aabdb3fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_cont_HC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (q : ℕ) {n : ℕ} {ι : Type} [Fintype ι] {F G : (Fin n → EuclideanSpace ℂ ι) → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun v => F v * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) := by
  exact (hF.mul (Complex.continuous_conj.comp hG)).mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp cont_HC))))
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
