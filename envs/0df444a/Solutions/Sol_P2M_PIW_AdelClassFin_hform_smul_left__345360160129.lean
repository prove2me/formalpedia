-- Prove2me | solution 1 for P2M_PIW_AdelClassFin_hform_smul_left__345360160129
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:35.944505+00:00
-- url     : https://prove2.me/submissions/e35454e9-5711-4742-a3e4-f3c39b745ca5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
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
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
namespace PIW.AdelClassFin
theorem _root_.solution (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) y = star c * hform (starRingEnd E) J x y := by
  unfold hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]
  ring
end PIW.AdelClassFin
