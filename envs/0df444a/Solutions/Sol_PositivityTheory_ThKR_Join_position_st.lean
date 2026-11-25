-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.position_st
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:40.790185+00:00
-- url     : https://prove2.me/submissions/0b74cd06-85ab-4cf5-bf81-011c85633239

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin
import Theorems.Thm_PositivityTheory_ThKR_Join_upd_comp

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
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) (i : ι)
    (u : Module.End ℂ (V i)) (hu : u ∈ Algebra.adjoin ℂ (Set.range (act i))) :
    ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i u) x ∈ P := by
  induction hu using Algebra.adjoin_induction with
  | mem u hu => obtain ⟨a, rfl⟩ := hu; exact hP i a
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, show (1 : Module.End ℂ (V i)) = LinearMap.id from rfl,
      Function.update_eq_self, map_id]
    exact P.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [PiTensorProduct.map_update_add]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    have := LinearMap.congr_fun (upd_comp (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i b) i a) x
    rw [Function.update_idem, Function.update_self] at this
    exact (show _ = map (Function.update _ i (a * b)) x from this) ▸ ha _ (hb x hx)
end PositivityTheory.ThKR.Join
