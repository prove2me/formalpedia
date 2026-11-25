-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.alt_dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:43.241421+00:00
-- url     : https://prove2.me/submissions/a0b20c91-5ef7-4acb-986c-8e18fc5f4f6a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_alt_perm
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (col : X → C) (ξ : TV n M X) (J : X → Fin n) (p q : X) (hpq : p ≠ q) (hc : col p = col q)
    (hJ : J p = J q) : alt (colG col) ξ J = 0 := by
  have ht : Equiv.swap p q ∈ colG col := by
    rw [mem_colG]
    intro r
    rcases eq_or_ne r p with rfl | hrp
    · simp [hc]
    rcases eq_or_ne r q with rfl | hrq
    · simp [hc]
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]
  have hJt : J ∘ Equiv.swap p q = J := by
    funext r
    simp only [Function.comp_apply]
    rcases eq_or_ne r p with rfl | hrp
    · simp [hJ]
    rcases eq_or_ne r q with rfl | hrq
    · simp [hJ]
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]
  have h := alt_perm col ξ J _ ht
  rw [hJt, Equiv.Perm.sign_swap hpq] at h
  have h2 : (2 : ℂ) • alt (colG col) ξ J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
end PositivityTheory.Rg.Cz.YoungTableau
