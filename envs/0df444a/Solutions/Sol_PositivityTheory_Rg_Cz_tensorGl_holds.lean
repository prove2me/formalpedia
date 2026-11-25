-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.tensorGl_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:15.708153+00:00
-- url     : https://prove2.me/submissions/afba7e26-fafc-4c8a-a323-ae924731ae90

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_glSum
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_omComm
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_eAt_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_eAt_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_pm_eAt
import Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_glLift
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_eAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_pm
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
open TensorGLSums
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl := by
  intro n M _ _ P _ _ E hE S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact glSum S _ _ (glLift E hE) (fun p a b c d => lift_comm_eAt _ _ _ _) fun p q a b c d => by
      by_cases hpq : p = q
      · subst hpq; rw [if_pos rfl, eAt_mul, eAt_mul]
      · rw [if_neg hpq, eAt_comm hpq, sub_self]
  · intro p hp a b
    have hsplit : tE S E a b = (lift (E a b) + eAt p a b) + ∑ q ∈ S.erase p, eAt q a b := by
      rw [tE, add_assoc]; congr 1; exact (Finset.add_sum_erase S (fun q => eAt q a b) hp).symm
    rw [hsplit]
    refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun q hq => ?_)
    · exact omComm (fun a b => lift (E a b)) (fun a b => eAt p a b) (glLift E hE)
        (fun a b c d => lift_comm_eAt _ _ _ _) (fun a b c d => eAt_mul p a b c d) a b
    · have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      refine Commute.sum_left _ _ _ fun a' _ => Commute.sum_left _ _ _ fun b' _ => ?_
      exact Commute.mul_left (lift_comm_eAt _ _ _ _) (eAt_comm (Ne.symm hqp) _ _ _ _)
  · intro σ hσ a b
    rw [tE, Commute, SemiconjBy, mul_add, add_mul, (lift_comm_pm _ σ).eq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    simp_rw [pm_eAt]
    exact Finset.sum_equiv σ (fun p => (hσ p).symm) fun p _ => rfl
  · intro σ p
    simp only [Om, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← (lift_comm_pm _ σ).eq, mul_assoc, pm_eAt, mul_assoc]
end PositivityTheory.Rg.Cz
