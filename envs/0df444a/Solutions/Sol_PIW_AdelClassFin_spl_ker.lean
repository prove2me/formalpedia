-- Prove2me | solution 1 for PIW.AdelClassFin.spl_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:51.693445+00:00
-- url     : https://prove2.me/submissions/7ce50885-4808-49c1-8513-163c51d021a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
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
namespace PIW.AdelClassFin
theorem _root_.solution {E : Type} [Field E] [StarRing E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E)
    (hΓ : (cT (starRingEnd E) V * J * V).det ≠ 0) (w : Fin m → E) :
    (cT (starRingEnd E) V * J) *ᵥ (w - V *ᵥ ((cT (starRingEnd E) V * J * V)⁻¹ *ᵥ
      ((cT (starRingEnd E) V * J) *ᵥ w))) = 0 := by
  simp [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
end PIW.AdelClassFin
