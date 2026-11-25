-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.adjugate_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:34.918803+00:00
-- url     : https://prove2.me/submissions/9c50e3f4-e284-40f7-a268-18a1bb22aec4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Intw
variable {A : Type*} [CommRing A] {n : ℕ}
namespace PI.OddDualWeyl.Intw
theorem _root_.solution {i j : Fin n} (h : i ≠ j) (c : A) :
    adjugate (transvection i j c) = transvection i j (-c) := by
  have h1 : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero]
  calc adjugate (transvection i j c)
      = adjugate (transvection i j c) * (transvection i j c * transvection i j (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = (adjugate (transvection i j c) * transvection i j c) * transvection i j (-c) := by
        rw [Matrix.mul_assoc]
    _ = transvection i j (-c) := by
        rw [adjugate_mul, det_transvection_of_ne i j h, one_smul, Matrix.one_mul]
end PI.OddDualWeyl.Intw
