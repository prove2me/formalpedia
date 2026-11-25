-- Prove2me | solution 1 for PI.ScRefExists.GWG.concl_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:23.224799+00:00
-- url     : https://prove2.me/submissions/a579088f-8275-4e8d-82ee-10db97c438d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_PI_ScRefExists_GWG_hG_zero_right
import Theorems.Thm_PI_ScRefExists_GWG_theta_mem
import Theorems.Thm_PI_ScRefExists_GWG_ite_mem
import Theorems.Thm_PI_ScRefExists_GWG_ge_one
import Theorems.Thm_PI_ScRefExists_GWG_gL_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
namespace PI.ScRefExists.GWG
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) :
    Concl I 1 r k θ e f M := by
  have hz0 : ∀ x : Fin I.n → I.E, hG I x 0 = 0 := hG_zero_right I
  refine ⟨0, fun _ => 0, fun _ => 0, I.L.zero_mem, fun _ => ⟨I.L.zero_mem, I.L.zero_mem⟩,
    fun a => ⟨hz0 _, hz0 _⟩, fun a i => ⟨hz0 _, hz0 _, hz0 _, hz0 _⟩, ?_, ?_, ?_, ?_⟩
  · rw [hz0, zero_add]; exact ge_one I (one_mem _)
  · intro i
    simp only [hz0, mul_zero]
    exact ⟨ge_one I (zero_mem _), ge_one I (zero_mem _)⟩
  · intro i j
    exact ge_one I (mul_mem (theta_mem I θ) (sub_mem (by rw [hz0]; exact zero_mem _) (ite_mem I (p := i = j))))
  · intro y hy
    apply Submodule.mem_sup_right
    have := gL_mem I 1 hy
    rwa [Nat.cast_one, one_smul] at this
end PI.ScRefExists.GWG
