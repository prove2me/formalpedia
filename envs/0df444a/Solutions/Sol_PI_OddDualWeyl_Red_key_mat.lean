-- Prove2me | solution 1 for PI.OddDualWeyl.Red.key_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:28.652079+00:00
-- url     : https://prove2.me/submissions/d5ae7511-d44d-42b0-b6ac-b38f72c1c0d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_adj
import Theorems.Thm_PI_OddDualWeyl_Red_adj_key

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
variable {K : Type*} [Field K] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) :
    cM gᵀ * dualM K k = (C g.det : MvPolynomial (Fin k × Fin k) K) • (dualM K k).map (sbs (cM g⁻¹ * genM K k)) := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (congrFun (adj_key g hd) (Fin.rev j)) i
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    smul_eq_mul, PI.OddDualWeyl.dualM, cM] at h ⊢
  rw [sbs_adj]
  first
  | (rw [← h]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _)
  | (refine Eq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_; exact h)
  | simpa [mul_comm] using h
end PI.OddDualWeyl.Red
