-- Prove2me | solution 1 for PIW.AdelClassFin.hform_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:18.916629+00:00
-- url     : https://prove2.me/submissions/e34f2cb5-5bac-40ef-a4b3-465128a2b84e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Theorems.Thm_PIW_AdelClassFin_hform_eq
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
open Formalism.UG
open scoped Matrix
variable {E : Type} [Field E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution {n : Type} [Fintype n] (J : Matrix n n E) (x x' y : n → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform_eq, star_add, add_dotProduct]
end PIW.AdelClassFin
