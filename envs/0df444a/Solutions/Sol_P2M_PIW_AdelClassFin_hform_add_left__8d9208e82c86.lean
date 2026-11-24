-- Prove2me | solution 1 for P2M_PIW_AdelClassFin_hform_add_left__8d9208e82c86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:37.337995+00:00
-- url     : https://prove2.me/submissions/b8db1882-68c3-4232-8510-d6b0c6b40d1e

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
theorem _root_.solution (x x' y : Fin m → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform, map_add, add_mul, Finset.sum_add_distrib]
end PIW.AdelClassFin
