-- Prove2me | solution 1 for PI.GGConvScalarW.psiU_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:18.036173+00:00
-- url     : https://prove2.me/submissions/a797487a-15d6-402f-b412-39d7effd55d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_superdiag_mul

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) :
    psiU ψ₀ (x * y) = psiU ψ₀ x * psiU ψ₀ y := by
  unfold psiU
  rw [Units.val_mul, superdiag_mul hx hy, AddChar.map_add_eq_mul]
end PI.GGConvScalarW
