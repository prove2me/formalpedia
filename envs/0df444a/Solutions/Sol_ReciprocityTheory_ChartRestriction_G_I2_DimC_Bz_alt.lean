-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Bz_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:31.268125+00:00
-- url     : https://prove2.me/submissions/fd455f51-6027-4f48-a06b-f36b84395d51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Hf_self_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Bz_apply

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
theorem _root_.solution (x : lat Y.b) : Bz Y x x = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Bz_apply, Int.cast_zero, Hf_self_im]
end ReciprocityTheory.ChartRestriction.G.I2.DimC
