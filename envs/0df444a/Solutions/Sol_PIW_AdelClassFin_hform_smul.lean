-- Prove2me | solution 1 for PIW.AdelClassFin.hform_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:51.960152+00:00
-- url     : https://prove2.me/submissions/d7f0b655-8a12-423a-989a-86912b6cf833

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
theorem _root_.solution {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c c' : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) (c' • y) = star c * c' * hform (starRingEnd E) J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PIW.AdelClassFin
