-- Prove2me | solution 1 for PIW.AdelClassFin.cT_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:23.725798+00:00
-- url     : https://prove2.me/submissions/381b4cf9-f469-4760-87f6-1bb73de72c4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
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
theorem _root_.solution {a b : Type} (A : Matrix a b E) : cT (starRingEnd E) A = Aᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, starRingEnd_apply]
end PIW.AdelClassFin
