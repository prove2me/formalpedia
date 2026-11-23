-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.fd_uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:32.722647+00:00
-- url     : https://prove2.me/submissions/3ea4e1ba-3bba-42f6-a1d8-24be1ce6904e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (b : Basis ι ℝ V) {x β1 β2 : V} (h1 : β1 ∈ span ℤ (range b))
    (h2 : β2 ∈ span ℤ (range b)) (hx1 : β1 + x ∈ ZSpan.fundamentalDomain b)
    (hx2 : β2 + x ∈ ZSpan.fundamentalDomain b) : β1 = β2 := by
  have := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b := b) x).unique
    (y₁ := ⟨β1, h1⟩) (y₂ := ⟨β2, h2⟩) hx1 hx2
  exact congrArg Subtype.val this
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
