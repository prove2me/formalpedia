-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_isSecOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:24.446836+00:00
-- url     : https://prove2.me/submissions/dcef62ca-2993-4e32-894d-85f7e6605b56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


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
theorem _root_.solution {la : La} {U V : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a)
    (hVU : V ⊆ U) : A.IsSecOn la V a := by
  unfold WeightedAtlas.IsSecOn at h ⊢
  exact And.intro (fun i => (h.1 i).mono (fun v hv => ⟨hv.1, hVU hv.2⟩))
    (fun i j y hy => h.2 i j y (hVU hy))
end ReciprocityTheory.L2DbarEstimates.Y
