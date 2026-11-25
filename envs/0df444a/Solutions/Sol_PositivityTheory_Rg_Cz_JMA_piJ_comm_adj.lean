-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.piJ_comm_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:16.489952+00:00
-- url     : https://prove2.me/submissions/5a91267e-a056-4056-888d-57c301627c23

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_comm_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_mul_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_mul_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_list_prod_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pair_comm
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (u : ℂ)
    (i : Fin m) : Commute (PiJ (m + 1) E u) (pm (Equiv.swap i.castSucc i.succ)) := by
  have hij : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 = i.succ := by simp
  show Commute (List.ofFn fun j : Fin (m + 1) => algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) u + xJ E j).prod _
  apply list_prod_comm _ _ i (by simp)
  · intro t ht h1 h2
    rw [List.getElem_ofFn]
    refine Commute.add_left (Algebra.commutes u _) ?_
    refine (swap_comm_xJ hT hE ⟨t, by simpa using ht⟩ i.castSucc i.succ ?_ ?_).symm
    · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
      omega
    · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
      omega
  · simp only [List.getElem_ofFn]
    exact pair_comm u _ _ _ (xJ_comm hT hE _ _) (xJ_mul_swap hT hE _ _ hij) (swap_mul_xJ hT hE _ _ hij)
end PositivityTheory.Rg.Cz.JMA
