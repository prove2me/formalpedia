-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.conj_sub_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:16.802792+00:00
-- url     : https://prove2.me/submissions/983b18ca-6497-4457-899d-a40c9ef375c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_inv
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_mulVec
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
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) : (Amat ε e f s * g * Amat ε e f s⁻¹ - 1) *ᵥ y =
      Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ y) := by
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Amat_mulVec, Amat_mulVec, sub_mulVec,
    one_mulVec]
  have := (Alin ε e f s).map_sub (g *ᵥ Afun ε e f s⁻¹ y) (Afun ε e f s⁻¹ y)
  simp only [Alin_apply] at this
  rw [this, A_inv hG s hs]
end PI.NMeasInv.UnitaryGroupMassFormula
