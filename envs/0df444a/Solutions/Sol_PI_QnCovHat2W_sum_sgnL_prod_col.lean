-- Prove2me | solution 1 for PI.QnCovHat2W.sum_sgnL_prod_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:12.911607+00:00
-- url     : https://prove2.me/submissions/f61c55f5-6049-42be-8b9e-a9985857aaa1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Fin N) :
    ∑ d : Fin N → Fin N, sgnL d id * ∏ k, Q (d k) (y k) = sgnL y id * Q.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun d => ∏ k, Q (d k) (y k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => Q i (y k)).det = sgnL y id * Q.det := by
    have h3 : (Matrix.of fun i k => Q i (y k)) =
        Q * (Matrix.of fun k j => if y k = id j then (1 : ℂ) else 0).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_mul, Matrix.det_transpose, mul_comm]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp
end PI.QnCovHat2W
