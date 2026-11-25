-- Prove2me | solution 1 for PIW.AdelClassFin.hform_self_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:34.073298+00:00
-- url     : https://prove2.me/submissions/b7e846a9-c9e7-4d10-9f2c-b49d9056bf33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
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
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : IsHerm (starRingEnd E) J)
    (x : Fin m → E) : star (hform (starRingEnd E) J x x) = hform (starRingEnd E) J x x := by
  have hij : ∀ i j, star (J j i) = J i j := fun i j => by
    have h1 := congrFun (congrFun hJ i) j
    simpa [cT, starRingEnd_apply] using h1
  simp only [hform, starRingEnd_apply, star_sum, star_mul', star_star, hij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PIW.AdelClassFin
