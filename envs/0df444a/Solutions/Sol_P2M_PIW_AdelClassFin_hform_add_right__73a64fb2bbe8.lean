-- Prove2me | solution 1 for P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:23.394135+00:00
-- url     : https://prove2.me/submissions/c691611a-f738-489b-a9e0-ea65e3a69e32

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
theorem _root_.solution (x y y' : Fin m → E) :
    hform (starRingEnd E) J x (y + y') = hform (starRingEnd E) J x y + hform (starRingEnd E) J x y' := by
  simp [hform, mul_add, Finset.sum_add_distrib]
end PIW.AdelClassFin
