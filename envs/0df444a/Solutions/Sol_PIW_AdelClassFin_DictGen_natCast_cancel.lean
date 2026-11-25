-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.natCast_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:51.985166+00:00
-- url     : https://prove2.me/submissions/713931f5-a9b9-48a4-9385-5639852de600

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
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
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution (N : ℕ) (hN : 0 < N) {a b : Fin I.n → I.E ⊗[I.F] Af I.F}
    (h : (N : I.E ⊗[I.F] Af I.F) • a = (N : I.E ⊗[I.F] Af I.F) • b) : a = b := by
  have hu : IsUnit (N : (I.E ⊗[I.F] Af I.F)) := by
    have h0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := (IsUnit.mk0 _ h0).map (algebraMap I.F (I.E ⊗[I.F] Af I.F))
    rwa [map_natCast] at h1
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact hu.mul_left_cancel hi
end PIW.AdelClassFin.DictGen
