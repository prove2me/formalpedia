-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.A_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:47.870375+00:00
-- url     : https://prove2.me/submissions/9d567a1b-5f90-4290-9f79-454f11b14df1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_A
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_A
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_A
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
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s u : Fin r → ℝ) (v : Fin n → ℂ) :
    Afun ε e f s (Afun ε e f u v) = Afun ε e f (s * u) v := by
  show ∑ b, ((s b : ℂ) * hJ ε (f b) (Afun ε e f u v)) • e b +
      ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) (Afun ε e f u v)) • f b + Pw ε e f (Afun ε e f u v) =
      Afun ε e f (s * u) v
  rw [Pw_A hG]
  simp only [f_A hG, e_A hG]
  simp only [Afun, Pi.mul_apply, Complex.ofReal_mul, mul_inv, mul_assoc]
end PI.NMeasInv.UnitaryGroupMassFormula
