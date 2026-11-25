-- Prove2me | solution 1 for PIW.AdelClassFin.mInj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:50.35237+00:00
-- url     : https://prove2.me/submissions/cbfc731b-09f2-4154-aa73-ea185788f4e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
import Theorems.Thm_PIW_AdelClassFin_dictTop_mul_inv
import Theorems.Thm_PIW_AdelClassFin_dictTop_inv_mul
import Theorems.Thm_PIW_AdelClassFin_dictTop_fmat_mul
import Theorems.Thm_PIW_AdelClassFin_dictTop_into
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
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hG : MGen) : MInj := by
  intro I x y h
  refine ⟨x⁻¹ * y, fun z => ?_, (mul_inv_cancel_left x y).symm⟩
  show z ∈ I.Lf ↔ I.fmat (x⁻¹ * y) *ᵥ z ∈ I.Lf
  rw [dictTop_fmat_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hz
    exact dictTop_into hG I x y h z hz
  · intro hz
    have h2 := dictTop_into hG I y x h.symm _ hz
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h2
    rwa [← Matrix.mul_assoc (I.fmat x), dictTop_mul_inv, Matrix.one_mul, dictTop_inv_mul,
      Matrix.one_mulVec] at h2
end PIW.AdelClassFin
