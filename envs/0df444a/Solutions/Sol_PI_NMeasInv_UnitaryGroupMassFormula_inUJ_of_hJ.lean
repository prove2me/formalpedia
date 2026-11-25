-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.inUJ_of_hJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:58.591978+00:00
-- url     : https://prove2.me/submissions/6e9ba1e4-0a46-4eda-a344-363408a97d76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_mulVec_eq
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
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
omit hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε M := by
  unfold Formalism.REAL.inUJ
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec_eq] at this
  unfold hJ at this
  simpa [Matrix.mulVec_single_one, Pi.star_single] using this
end PI.NMeasInv.UnitaryGroupMassFormula
