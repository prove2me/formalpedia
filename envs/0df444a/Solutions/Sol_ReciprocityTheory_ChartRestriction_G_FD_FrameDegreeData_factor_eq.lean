-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:52:49.875365+00:00
-- url     : https://prove2.me/submissions/270f56f7-f55b-4580-b2d4-7077b73acd8f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (t q : ℝ) (ht : 0 < t) (hq : 0 ≤ q) (l : ℤ) :
    t ^ l * (t ^ 2 * q) ^ (-(l : ℝ) / 2) = q ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) hq]
  have h1 : (t ^ 2) ^ (-(l : ℝ) / 2) = (t ^ l)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_intCast]
  rw [h1, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht.ne'), one_mul]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
