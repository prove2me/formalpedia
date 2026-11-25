-- Prove2me | solution 1 for PI.GGConvScalarW.psiU_sgn_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:21.241452+00:00
-- url     : https://prove2.me/submissions/fd002a17-f1a4-42c7-8ca8-541a5d22cfbf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_superdiag_sgn_conj

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiU ψ₀ (sgn k * u * sgn k) * psiU ψ₀ u = 1 := by
  unfold psiU
  rw [show ((sgn k * u * sgn k : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = sgnM k * (u : Matrix (Fin k) (Fin k) F) * sgnM k from rfl,
    superdiag_sgn_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
end PI.GGConvScalarW
