-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.map_st
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:33.321778+00:00
-- url     : https://prove2.me/submissions/88f03305-f2f0-43ef-8799-4c4bd0d1c548

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin
import Theorems.Thm_PositivityTheory_ThKR_Join_upd_comp
import Theorems.Thm_PositivityTheory_ThKR_Join_position_st

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
theorem _root_.solution {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (u : ∀ i, Module.End ℂ (V i)) (hu : ∀ i, u i ∈ Algebra.adjoin ℂ (Set.range (act i))) : ∀ x ∈ P, map u x ∈ P := by
  have h : ∀ S : Finset ι, ∀ x ∈ P, map (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) x ∈ P := fun S => by
    induction S using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j S hj ih =>
      intro x hx
      have h1 := position_st act P hP j (u j) (hu j) _ (ih x hx)
      rw [← LinearMap.comp_apply, upd_comp] at h1
      have e : (fun i => if i ∈ insert j S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) =
          Function.update (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) j
            (u j ∘ₗ if j ∈ S then u j else LinearMap.id) := by
        funext i
        by_cases h : i = j
        · subst h; simp [hj]
        · simp [h]
      rw [e]
      exact h1
  simpa using h Finset.univ
end PositivityTheory.ThKR.Join
