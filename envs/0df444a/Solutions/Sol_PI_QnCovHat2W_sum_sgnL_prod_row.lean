-- Prove2me | solution 1 for PI.QnCovHat2W.sum_sgnL_prod_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:17.25759+00:00
-- url     : https://prove2.me/submissions/a88fc730-109a-4b6b-a2f1-0ac4d116e4d3

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
theorem _root_.solution {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → Fin N) :
    ∑ c : Fin N → Fin N, sgnL c id * ∏ k, P (x k) (c k) = sgnL x id * P.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun c => ∏ k, P (x k) (c k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => P (x k) i).det = sgnL x id * P.det := by
    have h3 : (Matrix.of fun i k => P (x k) i) =
        ((Matrix.of fun k j => if x k = id j then (1 : ℂ) else 0) * P).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_transpose, Matrix.det_mul]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp
end PI.QnCovHat2W
