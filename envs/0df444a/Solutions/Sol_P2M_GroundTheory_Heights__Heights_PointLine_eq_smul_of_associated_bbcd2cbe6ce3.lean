-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_eq_smul_of_associated_bbcd2cbe6ce3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:27.243962+00:00
-- url     : https://prove2.me/submissions/dc457d64-988b-4acc-b9d4-658ac0e4e3dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution {x y : Fin n → ℂ} (h : Associated (pairing y) (pairing x)) :
    ∃ t : ℂ, x = t • y := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hc⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  refine ⟨c, funext fun j => ?_⟩
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) hu
  rw [hc, mul_comm, coeff_C_mul, coeff_pairing, coeff_pairing] at h
  rw [← h, Pi.smul_apply, smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.PointLine
