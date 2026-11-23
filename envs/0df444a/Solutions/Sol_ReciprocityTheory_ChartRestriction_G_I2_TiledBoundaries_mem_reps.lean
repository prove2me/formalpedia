-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.mem_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:07.624516+00:00
-- url     : https://prove2.me/submissions/9d0d7e14-47d8-43ed-a74d-2e00dbb478f7

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
theorem _root_.solution {bA bB : Basis ι ℝ V} {c : V} :
    c ∈ reps bA bB ↔ c ∈ ZSpan.fundamentalDomain bA ∧ c ∈ span ℤ (range bB) := by
  unfold reps
  rw [Set.Finite.mem_toFinset]
  exact Iff.intro (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.1, h.2⟩)
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
