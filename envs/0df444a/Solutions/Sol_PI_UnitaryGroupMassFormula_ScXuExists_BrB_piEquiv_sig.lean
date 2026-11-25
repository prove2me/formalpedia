-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.piEquiv_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:01.069985+00:00
-- url     : https://prove2.me/submissions/fc26af9c-26ad-456e-affd-01b7e48f28f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hσσ : ∀ r, σ (σ r) = r) (hb : Function.Bijective (piHom σ p1)) (r : R) :
    piEquiv σ p1 hb (σ r) = (piEquiv σ p1 hb r).swap := by
  ext <;> simp [piEquiv, piHom, hσσ]
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
