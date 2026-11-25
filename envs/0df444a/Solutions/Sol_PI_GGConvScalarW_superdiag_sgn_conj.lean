-- Prove2me | solution 1 for PI.GGConvScalarW.superdiag_sgn_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:40.132105+00:00
-- url     : https://prove2.me/submissions/25fc66ea-9729-4e99-9fee-a2fd8510b049

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) F) :
    superdiag k (sgnM (F := F) k * A * sgnM (F := F) k) = - superdiag k A := by
  unfold superdiag
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hs : (-1 : F) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [sgn_conj_apply, h, pow_succ]
    linear_combination (-(A i j)) * hs
  · rw [neg_zero]
end PI.GGConvScalarW
