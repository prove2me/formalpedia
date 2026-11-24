-- Prove2me | solution 1 for PIW.AdelClassFin.cT_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:27.749213+00:00
-- url     : https://prove2.me/submissions/29184ac3-b5f3-4c03-933b-3e5936d13514

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Theorems.Thm_PIW_AdelClassFin_cT_star
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
theorem _root_.solution {n k : Type} [Fintype n] (J : Matrix n n E) (V : Matrix n k E) (z : n → E) (i : k) :
    ((cT (starRingEnd E) V * J) *ᵥ z) i = hform (starRingEnd E) J (fun r => V r i) z := by
  rw [hform_eq, ← Matrix.mulVec_mulVec, cT_star]
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
end PIW.AdelClassFin
