-- Prove2me | solution 1 for PI.GGConvScalarW.sumPsi_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:42.794957+00:00
-- url     : https://prove2.me/submissions/23045f47-7a67-48d5-8acc-9f28a75da908

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
import Theorems.Thm_PI_GGConvScalarW_psiNat_mul_uni
import Theorems.Thm_PI_GGConvScalarW_psiU_ne_zero


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
theorem _root_.solution (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) :
    (∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) * π u = (psiU ψ₀ u)⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x := by
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_mul_assoc, ← map_mul, psiNat_mul_uni ψ₀ x hu, smul_smul]
  congr 1
  field_simp [psiU_ne_zero ψ₀ u]
end PI.GGConvScalarW
