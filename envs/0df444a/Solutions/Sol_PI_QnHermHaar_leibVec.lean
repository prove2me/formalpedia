-- Prove2me | solution 1 for PI.QnHermHaar.leibVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:42.37742+00:00
-- url     : https://prove2.me/submissions/9097a937-f6df-4f6b-af4e-89d3c17c6b7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Theorems.Thm_PI_QnHermHaar_commSumA
import Theorems.Thm_PI_QnHermHaar_commSumB
import Theorems.Thm_PI_QnHermHaar_smulComm
import Theorems.Thm_PI_QnHermHaar_qpApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0) (a b c : Fin m) :
    Econj E P Q a b * vecC Q Y c - vecC Q Y c * Econj E P Q a b = if a = c then -vecC Q Y b else 0 := by
  simp only [Econj, vecC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  have e : ∀ i j : Fin m, P i a * Q b j * Q c i = Q b j * (Q c i * P i a) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP c a]
  split_ifs with h1 h2 h2
  · simp [Finset.sum_neg_distrib]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp
end PI.QnHermHaar
