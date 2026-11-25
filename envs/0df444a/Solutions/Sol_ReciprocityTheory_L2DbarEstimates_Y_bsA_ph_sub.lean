-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_ph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:33:06.339364+00:00
-- url     : https://prove2.me/submissions/7936ee4f-7687-4064-8598-5c98912a05c8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA

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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (la mu : La) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (la - mu) i y = A.ph la i y - A.ph mu i y := by
  have h := A.ph_add (la - mu) mu i y hi
  rw [sub_add_cancel] at h
  linarith
end ReciprocityTheory.L2DbarEstimates.Y
