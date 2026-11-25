-- Prove2me | solution 1 for PI.GGConvScalarW.isUTm_sgn_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:50.783108+00:00
-- url     : https://prove2.me/submissions/7c4ffdab-c795-483d-8d8e-56a2e9d65d7b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_sgn_conj_apply

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
theorem _root_.solution {A : Matrix (Fin k) (Fin k) F} (h : IsUTm A) : IsUTm (sgnM (F := F) k * A * sgnM (F := F) k) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [sgn_conj_apply, h.1, mul_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  · rw [sgn_conj_apply, h.2 i j hij, mul_zero, zero_mul]
end PI.GGConvScalarW
