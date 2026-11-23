-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Cchi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:49.625229+00:00
-- url     : https://prove2.me/submissions/64a14d57-2022-47d6-8bc2-30d5be92ff88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rd_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (m : ℕ) : 0 ≤ Cchi (E := E) m := by
  unfold Cchi RR
  have := rd_nonneg (E := E)
  positivity
end ReciprocityTheory.ChartRestriction.G.I2
