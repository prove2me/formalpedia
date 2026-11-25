-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_isOpen_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:22:34.866286+00:00
-- url     : https://prove2.me/submissions/1f1899f9-6813-4225-aa3a-77f4f61df9a1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (i : ι) : IsOpen (flO A w0 i) := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  have hc : ContinuousOn (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hw.1 i).continuousOn
    simpa using this
  unfold flO
  exact hc.isOpen_inter_preimage (A.chart i).open_target (isOpen_ne (x := (0 : ℂ)))
end ReciprocityTheory.L2DbarEstimates.Y
