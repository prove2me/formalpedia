-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.mod_q_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:43.31527+00:00
-- url     : https://prove2.me/submissions/ae08a75d-5513-4bbd-95fb-0757150f0021

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_mul
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : ModQHom := by
  unfold ModQHom
  intro G _ K hK
  have hk1 : ∀ k ∈ K, dIdx K k = 1 := by
    intro k hk
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro y hy
    refine Subgroup.mem_map.2 ⟨k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨fun x y => modQ_mul K hK x y, fun k hk => ?_, fun x hx => ?_⟩
  · unfold modQ
    rw [hk1 k hk, hk1 k⁻¹ (K.inv_mem hk)]
    norm_num
  · unfold modQ at hx
    have hne : (dIdx K x⁻¹ : ℚ) ≠ 0 := by exact_mod_cast hK x⁻¹
    rw [div_eq_one_iff_eq hne] at hx
    exact_mod_cast hx
end PI.UnitaryGroupMassFormula.AdIndexEq
