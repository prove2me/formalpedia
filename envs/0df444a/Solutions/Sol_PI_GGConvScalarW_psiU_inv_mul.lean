-- Prove2me | solution 1 for PI.GGConvScalarW.psiU_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:25.416808+00:00
-- url     : https://prove2.me/submissions/5d6444f5-ba80-448d-8686-bbd95729a6b4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_isUni_inv
import Theorems.Thm_PI_GGConvScalarW_psiU_mul
import Theorems.Thm_PI_GGConvScalarW_psiU_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGConvScalarW
theorem _root_.solution (ψ₀ : AddChar F ℂ) {x : GL (Fin k) F} (hx : IsUni k x) :
    psiU ψ₀ x⁻¹ * psiU ψ₀ x = 1 := by
  rw [← psiU_mul ψ₀ (isUni_inv hx) hx, inv_mul_cancel, psiU_one]
end PI.GGConvScalarW
