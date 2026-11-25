-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.reps_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:29.26257+00:00
-- url     : https://prove2.me/submissions/6f8b7c64-d8e6-4b91-8b21-da7de796368b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_reps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_exists

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
theorem _root_.solution (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (b : V) (hb : b ∈ span ℤ (range bB)) :
    ∃! c, c ∈ reps bA bB ∧ b - c ∈ span ℤ (range bA) := by
  obtain ⟨β, hβ, hβb⟩ := fd_exists bA b
  refine ⟨β + b, ⟨mem_reps.2 ⟨hβb, add_mem (hAB hβ) hb⟩, ?_⟩, ?_⟩
  · have e : b - (β + b) = -β := by abel
    rw [e]
    exact neg_mem hβ
  · rintro c' ⟨hc'R, hc'A⟩
    have hc'F := (mem_reps.1 hc'R).1
    have e := fd_uniq bA (neg_mem hc'A) hβ (x := b)
      (by convert hc'F using 1; abel) hβb
    rw [← e]
    abel
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
