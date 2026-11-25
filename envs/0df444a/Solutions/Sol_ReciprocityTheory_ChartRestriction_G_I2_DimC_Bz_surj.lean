-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Bz_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:09.452155+00:00
-- url     : https://prove2.me/submissions/a328ee24-e525-402f-aa02-f7ba9004f3c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
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
theorem _root_.solution (φ : lat Y.b →ₗ[ℤ] ℤ) : ∃ x, Bz Y x = φ := by
  obtain ⟨x, hx, h⟩ := Y.perfect φ.toAddMonoidHom
  refine ⟨⟨x, hx⟩, LinearMap.ext fun y => ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [Bz_apply]
  have h' := h y
  rw [LinearMap.toAddMonoidHom_coe] at h'
  exact h'.symm
end ReciprocityTheory.ChartRestriction.G.I2.DimC
