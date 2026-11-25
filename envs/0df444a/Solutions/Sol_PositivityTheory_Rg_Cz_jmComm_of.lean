-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.jmComm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:08.201707+00:00
-- url     : https://prove2.me/submissions/d5adaeaa-ba22-444d-b553-2eaffa9c1d68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_comm_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_mul_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_piJ_comm
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
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm := by
  intro hT n M _ _ E hE m
  refine ⟨JMA.xJ_comm hT hE, fun i j h => ⟨JMA.xJ_mul_swap hT hE i j h, fun k hk1 hk2 => ?_⟩,
    fun u σ => JMA.piJ_comm hT hE m u σ⟩
  have e1 := Fin.val_ne_of_ne hk1
  have e2 := Fin.val_ne_of_ne hk2
  refine (JMA.swap_comm_xJ hT hE k i j ?_ ?_).symm
  · simp only [Fin.lt_iff_val_lt_val]
    omega
  · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
end PositivityTheory.Rg.Cz
