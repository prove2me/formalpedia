-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_fund
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:46.406644+00:00
-- url     : https://prove2.me/submissions/cd497f3a-2c0e-471e-a87a-89ae2b8f16ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_reps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_reps_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
section Tile
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
private theorem mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain {bA bB : Basis ι ℝ V} {x : V} :
    x ∈ tileT bA bB ↔ ∃ c ∈ reps bA bB, x - c ∈ ZSpan.fundamentalDomain bB := by
  unfold tileT
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
private theorem measurableSet_tileT (bA bB : Basis ι ℝ V) :
    MeasurableSet (tileT bA bB) := by
  unfold tileT
  exact Finset.measurableSet_biUnion _ fun c _ =>
    (ZSpan.fundamentalDomain_measurableSet bB).preimage (continuous_sub_right c).measurable
variable (μ : Measure V) [μ.IsAddHaarMeasure]
end Tile
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (μ : Measure V) :
    IsAddFundamentalDomain (span ℤ (range bA)).toAddSubgroup (tileT bA bB) μ := by
  have hv : ∀ (g : (span ℤ (range bA)).toAddSubgroup) (y : V), g +ᵥ y = (g : V) + y :=
    fun _ _ => rfl
  refine IsAddFundamentalDomain.mk' (measurableSet_tileT bA bB).nullMeasurableSet ?_
  intro x
  obtain ⟨β, hβ, hβx⟩ := fd_exists bB x
  obtain ⟨c, ⟨hc, hc'⟩, huniq⟩ := reps_unique bA bB hAB (-β) (neg_mem hβ)
  have hg : c + β ∈ span ℤ (range bA) := by
    have := neg_mem hc'
    rwa [neg_sub, sub_neg_eq_add] at this
  refine ⟨⟨c + β, hg⟩, ?_, ?_⟩
  · beta_reduce
    rw [hv, mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain]
    refine ⟨c, hc, ?_⟩
    change c + β + x - c ∈ _
    convert hβx using 1
    abel
  · rintro ⟨g, hgA⟩ hgx
    rw [hv, mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain] at hgx
    obtain ⟨c', hc'R, hc'x⟩ := hgx
    change g + x - c' ∈ _ at hc'x
    have hgA' : g ∈ span ℤ (range bA) := hgA
    have hc'B : c' ∈ span ℤ (range bB) := (mem_reps.1 hc'R).2
    have h1 : g - c' = β := fd_uniq bB (sub_mem (hAB hgA') hc'B) hβ
      (by convert hc'x using 1; abel) hβx
    have h2 : c' = c := huniq c' ⟨hc'R, by
      have e : -β - c' = -g := by rw [← h1]; abel
      rw [e]
      exact neg_mem hgA'⟩
    apply Subtype.ext
    change g = c + β
    rw [← h2, ← h1]
    abel
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
