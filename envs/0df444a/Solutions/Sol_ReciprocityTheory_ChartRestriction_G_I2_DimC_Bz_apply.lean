-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Bz_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:55.775204+00:00
-- url     : https://prove2.me/submissions/932ba3ee-d46a-4709-99e2-cba49eabeef2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (x y : lat Y.b) : ((Bz Y x y : ℤ) : ℝ) = (Hf (x : EuclideanSpace ℂ ι) y).im := by
  simp only [Bz, LinearMap.mk₂_apply]
  exact nz_eq Y x.2 y.2
end ReciprocityTheory.ChartRestriction.G.I2.DimC
