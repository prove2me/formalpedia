-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.L_le_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:01.199374+00:00
-- url     : https://prove2.me/submissions/9e088d3f-506b-4037-849b-142494ebd2e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : span ℤ (range X.b) ≤ span ℤ (range (bP X hq hπ)) := fun x hx => (mem_P X hq hπ x).mpr (hπ.2.1 x hx)
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
