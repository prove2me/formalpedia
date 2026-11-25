-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:33.066906+00:00
-- url     : https://prove2.me/submissions/f7826b58-3343-4b51-b103-5c5ecfff03bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_reps_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_measure

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
theorem _root_.solution (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (h : V → ℝ) (hc : Continuous h)
    (hper : ∀ β ∈ span ℤ (range bB), ∀ x, h (x + β) = h x) :
    ⨍ x in ZSpan.fundamentalDomain bA, h x ∂μ = ⨍ x in ZSpan.fundamentalDomain bB, h x ∂μ := by
  have hcard : ((reps bA bB).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨0, reps_zero bA bB⟩)
  rw [setAverage_eq, setAverage_eq, tile_integral μ bA bB hAB h hc hper,
    tile_measure μ bA bB hAB, smul_eq_mul, smul_eq_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hcard, one_mul]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
