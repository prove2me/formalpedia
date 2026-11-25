-- Prove2me | solution 1 for PI.ScRefExists.WF.fam_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:20.336735+00:00
-- url     : https://prove2.me/submissions/d60dd322-c6c0-48a0-be3b-2a158c93a08f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WFrameOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WF_L_le_LA
import Theorems.Thm_PI_ScRefExists_WF_hG_e_proj
import Theorems.Thm_PI_ScRefExists_WF_hG_f_proj
import Theorems.Thm_PI_ScRefExists_WF_hG_sub_right
import Theorems.Thm_PI_ScRefExists_WF_proj_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}
namespace PI.ScRefExists.WF
theorem _root_.solution (hp : p.Prime) (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p)
    (hW : ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)) :
    ⊤ ≤ Submodule.span I.E (Set.range (fam e f w)) := by
  rw [← I.L_span, Submodule.span_le]
  intro y hy
  have hyA : y ∈ LA I p := L_le_LA hy
  have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
    apply hW _ (sub_mem hyA (proj_mem hp heA hfA hyA))
    intro a
    rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  have key : ∀ z ∈ Submodule.span (Ap I p) (Set.range w),
      z ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ (c : I.E) hx
  have hp' : proj e f y ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    unfold proj
    refine Submodule.sum_mem _ fun a _ => add_mem ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl a), rfl⟩)
  have := add_mem hp' (key _ hz)
  simpa using this
end PI.ScRefExists.WF
