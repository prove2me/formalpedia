-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DetIdxW.idx_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:43.20105+00:00
-- url     : https://prove2.me/submissions/0ce339f2-2c81-4df8-a9cc-7d3c06270ea5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_apply_9834e349ebaa
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_oLat_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_vm_apply
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.DetIdxW
theorem _root_.solution (γ : Matrix (Fin k) (Fin k) (𝓞 K)) (hγ : γ.det ≠ 0) :
    ((oLat K k).toAddSubgroup.map (vm (γ.map (algebraMap (𝓞 K) K)))).relIndex (oLat K k).toAddSubgroup =
      (Algebra.norm ℤ γ.det).natAbs := by
  classical
  have hGinj : Function.Injective γᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra hne
    exact hγ (Matrix.det_transpose γ ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨t, hne, ht⟩)
  let Gz : (Fin k → 𝓞 K) →ₗ[ℤ] (Fin k → 𝓞 K) := γᵀ.mulVecLin.restrictScalars ℤ
  have hGz : Function.Injective Gz := hGinj
  let e := LinearEquiv.ofInjective Gz hGz
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range Gz) e
  have hcomp : (LinearMap.range Gz).subtype ∘ₗ
      (e : (Fin k → 𝓞 K) →+ LinearMap.range Gz).toIntLinearMap = Gz := by
    ext x
    rfl
  have hdetG : LinearMap.det γᵀ.mulVecLin = γ.det := by
    rw [← Matrix.det_transpose γ]
    exact LinearMap.det_toLin' γᵀ
  rw [hcomp, LinearMap.det_restrictScalars, hdetG] at hcard
  have hcomm : (vm (γ.map (algebraMap (𝓞 K) K))).comp (ιc K k) = (ιc K k).comp Gz.toAddMonoidHom := by
    refine AddMonoidHom.ext fun t => funext fun j => ?_
    simp only [AddMonoidHom.comp_apply, vm_apply, ιc_apply, LinearMap.toAddMonoidHom_coe]
    simp [Gz, Matrix.vecMul, dotProduct, ιc_apply, map_sum, map_mul, mul_comm]
  have hr : (⊤ : AddSubgroup (Fin k → 𝓞 K)).map Gz.toAddMonoidHom = (LinearMap.range Gz).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  rw [oLat_eq, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _ ιc_inj, AddSubgroup.relIndex_top_right, hr, hcard,
    AddSubgroup.index_eq_card]
  rfl
end PI.UnitaryGroupMassFormula.LCG.DetIdxW
