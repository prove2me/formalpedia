-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.mem_span_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:51.182321+00:00
-- url     : https://prove2.me/submissions/e30372eb-9b92-4f86-8102-9037e9ad98d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℝ V] {ι : Type} (b : Basis ι ℝ V)
    (e : V ≃ₗ[ℝ] V) (x : V) : x ∈ span ℤ (range (b.map e)) ↔ e.symm x ∈ span ℤ (range b) := by
  have h : range (b.map e) = ((e.restrictScalars ℤ : V ≃ₗ[ℤ] V) : V →ₗ[ℤ] V) '' range b := by
    ext y
    simp [Basis.map_apply]
  rw [h, Submodule.span_image, Submodule.mem_map_equiv]
  try rfl
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
