-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.listSub_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:04.974749+00:00
-- url     : https://prove2.me/submissions/bcbdd26f-b4da-4051-87da-1c56328159f9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_commute
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_pairwise
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
open PositivityTheory.Rg.Cz.ChainP
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (A : Module.End ℂ V) {n : ℕ} (l : Fin n → ℂ) (c : Fin n)
    (h0 : (List.ofFn fun k => A - algebraMap ℂ _ (l k)).prod = 0) :
    (((List.ofFn l).erase (l c)).map fun r => A - algebraMap ℂ _ r).prod * (A - algebraMap ℂ _ (l c)) = 0 := by
  have hm : l c ∈ List.ofFn l := by simp
  have h1 : ((List.ofFn l).map fun r => A - algebraMap ℂ (Module.End ℂ V) r).prod = 0 := by
    rw [List.map_ofFn]
    exact h0
  rw [((List.perm_cons_erase hm).map _).prod_eq' (listSub_pairwise A _), List.map_cons,
    List.prod_cons] at h1
  rw [(listSub_commute A _ ((Commute.refl A).sub_right (Algebra.commutes _ A).symm) _).eq]
  exact h1
end PositivityTheory.Rg.Cz.ChainP
