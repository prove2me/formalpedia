-- Prove2me | solution 1 for PIW.AdelClassFin.svR_hdot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:26:40.291635+00:00
-- url     : https://prove2.me/submissions/2afffb46-ffec-4129-88d1-13e6052b1fb1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
import Theorems.Thm_PIW_AdelClassFin_svR_hform
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
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) =
      star (fun k => φ (x k)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) := by
  rw [svR_hform hst]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]
end PIW.AdelClassFin
