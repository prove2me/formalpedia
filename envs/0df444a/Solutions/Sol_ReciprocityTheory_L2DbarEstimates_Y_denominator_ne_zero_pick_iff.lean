-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.denominator_ne_zero_pick_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:20.943802+00:00
-- url     : https://prove2.me/submissions/b7ec8877-94e7-466b-8dae-ee567b9f07e5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    w0 (A.pick y) y ≠ 0 ↔ w0 i y ≠ 0 := by
  obtain ⟨-, htr⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hg := A.g_ne L (A.pick y) i y (A.mem_pick y) hy
  rw [htr (A.pick y) i y trivial (A.mem_pick y) hy]
  exact ⟨fun h1 h2 => h1 (by rw [h2, mul_zero]), fun h1 => mul_ne_zero hg h1⟩
end ReciprocityTheory.L2DbarEstimates.Y
