-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.Aop_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:18.981594+00:00
-- url     : https://prove2.me/submissions/e2ba0742-1190-4a94-a1dd-0fab1804cd9c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_prod_one_apply
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution : (Aop (fun _ : P => (1 : Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ (TV n M P)) = 1 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Aop_apply, prod_one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Module.End.one_apply]
end PositivityTheory.Rg.Cz.TGK
