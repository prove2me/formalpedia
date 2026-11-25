-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:59.060955+00:00
-- url     : https://prove2.me/submissions/0e207544-b768-4e55-b16f-03c806792cc6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_int_D
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_deriv_D

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
namespace PositivityTheory.ThKOwn.SchI
theorem _root_.solution : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ where
  zero_eq x := by
    show (∫ a, iteratedFDeriv ℝ 0 (G a) x ∂μ) 0 = ∫ a, G a x ∂μ
    rw [ContinuousMultilinearMap.integral_apply (int_D hG hI 0 x)]
    simp only [iteratedFDeriv_zero_apply]
  fderiv m _ x := deriv_D hG hI m x
  cont m _ := continuous_iff_continuousAt.2 fun x => (deriv_D hG hI m x).continuousAt
end PositivityTheory.ThKOwn.SchI
