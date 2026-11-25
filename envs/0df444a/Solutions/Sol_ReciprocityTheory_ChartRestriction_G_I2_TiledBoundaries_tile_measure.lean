-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:17.547737+00:00
-- url     : https://prove2.me/submissions/b9c22cc0-27fe-4c02-ab20-3700577bd0ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_integral

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
variable (μ : Measure V) [μ.IsAddHaarMeasure]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB)) :
    μ.real (ZSpan.fundamentalDomain bA) =
      (reps bA bB).card * μ.real (ZSpan.fundamentalDomain bB) := by
  have := tile_integral μ bA bB hAB (fun _ => (1 : ℝ)) continuous_const
    (fun _ _ _ => rfl)
  simpa [setIntegral_const] using this
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
