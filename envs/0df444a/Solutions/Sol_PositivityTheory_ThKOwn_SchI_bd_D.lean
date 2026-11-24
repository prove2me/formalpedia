-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.bd_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:51.260822+00:00
-- url     : https://prove2.me/submissions/28e068b9-a763-4c20-b98b-8e3b1e42da04

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open PositivityTheory.ThKOwn.SchI
open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)
include hG hI
omit hG hI
namespace PositivityTheory.ThKOwn.SchI
theorem _root_.solution (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  have h := SchwartzMap.le_seminorm ℂ 0 j f x
  rwa [pow_zero, one_mul] at h
end PositivityTheory.ThKOwn.SchI
