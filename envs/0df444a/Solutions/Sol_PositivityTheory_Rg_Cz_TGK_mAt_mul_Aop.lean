-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.mAt_mul_Aop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:10.93238+00:00
-- url     : https://prove2.me/submissions/5315714d-d75a-48ff-802c-b933fcb77851

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_prod_split
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
theorem _root_.solution (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (mAt p A * Aop K : Module.End ℂ (TV n M P)) = Aop (Function.update K p (A * K p)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, mAt_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [prod_split p (fun q => Function.update K p (A * K p) q (I q) (J q))]
  simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_split p (fun q => K q (Function.update I p j q) (J q))]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun q hq => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]
end PositivityTheory.Rg.Cz.TGK
