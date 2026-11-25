-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.upd_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:58.348247+00:00
-- url     : https://prove2.me/submissions/05f2c914-77e0-43c4-bb69-56fc7072959b

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
namespace PositivityTheory.ThKR.Join
theorem _root_.solution (u : ∀ j, V j →ₗ[ℂ] V j) (i : ι) (a : V i →ₗ[ℂ] V i) :
    map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i a) ∘ₗ map u = map (Function.update u i (a ∘ₗ u i)) := by
  rw [← map_comp]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]
end PositivityTheory.ThKR.Join
