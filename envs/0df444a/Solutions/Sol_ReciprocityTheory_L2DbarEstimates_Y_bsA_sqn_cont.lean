-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_sqn_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:52:44.642804+00:00
-- url     : https://prove2.me/submissions/e5131165-5b4e-446f-a1c9-a2b073472f45

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_cont

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
theorem _root_.solution {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous (fun y => ∑ k, A.nsq la (w k) y)
  exact continuous_finset_sum _ (fun k _ => bsA_nsq_cont A (hw k))
end ReciprocityTheory.L2DbarEstimates.Y
