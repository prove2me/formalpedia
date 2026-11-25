-- Prove2me | solution 1 for PI.GGConvScalarW.psiNat_mul_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:32.015304+00:00
-- url     : https://prove2.me/submissions/7e18fc5d-9239-4691-932e-eed06def185a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
import Theorems.Thm_PI_GGConvScalarW_isUni_inv
import Theorems.Thm_PI_GGConvScalarW_isUni_mul
import Theorems.Thm_PI_GGConvScalarW_psiU_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PI.GGConvScalarW
theorem _root_.solution (ψ₀ : AddChar F ℂ) (z : GL (Fin k) F) {u : GL (Fin k) F} (hu : IsUni k u) :
    psiNat ψ₀ (z * u) = psiNat ψ₀ z * psiU ψ₀ u := by
  unfold psiNat
  by_cases hz : IsUni k z
  · rw [if_pos (isUni_mul hz hu), if_pos hz, psiU_mul ψ₀ hz hu]
  · have : ¬ IsUni k (z * u) := fun h => hz (by simpa using isUni_mul h (isUni_inv hu))
    rw [if_neg this, if_neg hz, zero_mul]
end PI.GGConvScalarW
