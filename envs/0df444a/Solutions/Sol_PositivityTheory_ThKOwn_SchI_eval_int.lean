-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.eval_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:39.766973+00:00
-- url     : https://prove2.me/submissions/1e9f314d-e780-4978-a368-7cc1d645a91e

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_J_apply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_int_J
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_taylor

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
theorem _root_.solution (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  have h1 : (∫ a, J k j (G a) ∂μ) x = ∫ a, J k j (G a) x ∂μ :=
    ((BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm (int_J hG hI k j)).symm
  rw [h1, ← (taylor hG hI).eq_iteratedFDeriv (m := j) (by exact_mod_cast le_top) x]
  simp only [J_apply, jet_apply]
  exact integral_smul _ _
end PositivityTheory.ThKOwn.SchI
