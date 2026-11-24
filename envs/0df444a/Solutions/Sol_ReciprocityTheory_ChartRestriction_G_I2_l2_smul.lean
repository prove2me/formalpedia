-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.l2_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:14.812629+00:00
-- url     : https://prove2.me/submissions/708e62cd-cda2-4c5c-a578-29d92e23444a

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
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (q : ℕ) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2 q (c • F) = ‖c‖ ^ 2 * X.l2 q F := by
  have h : ∀ v, X.ptN2 q (c • F) v = ‖c‖ ^ 2 * X.ptN2 q F v := by
    intro v
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  simp only [PT.l2, h]
  first
  | exact MeasureTheory.integral_const_mul _ _
  | exact MeasureTheory.integral_mul_left _ _
  | simp [MeasureTheory.average, MeasureTheory.integral_const_mul]
end ReciprocityTheory.ChartRestriction.G.I2
