-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.eq_zero_of_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:52.289248+00:00
-- url     : https://prove2.me/submissions/2871ae35-8c78-4f8c-be7a-731d916c4871

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (hdet : J.det ≠ 0) (w : Fin n → K) (h : ∀ z, H σ J w z = 0) : w = 0 := by
  have h1 : (σ ∘ w) ᵥ* J = 0 := by
    funext k
    have h2 := h (Pi.single k 1)
    rw [H, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h2
    exact h2
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have h3 := congrFun h2 i
  simpa using h3
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
