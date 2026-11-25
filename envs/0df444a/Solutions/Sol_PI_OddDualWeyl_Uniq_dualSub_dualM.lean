-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.dualSub_dualM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:16.39154+00:00
-- url     : https://prove2.me/submissions/f0e940fa-b03b-40bb-b4d3-f062670c3550

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
import Theorems.Thm_PI_OddDualWeyl_Uniq_mul_P
import Theorems.Thm_PI_OddDualWeyl_Uniq_P_transpose
import Theorems.Thm_PI_OddDualWeyl_Uniq_dualM_eq
import Theorems.Thm_PI_OddDualWeyl_Uniq_map_genM

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}
namespace PI.OddDualWeyl.Uniq
theorem _root_.solution (hk : k ≠ 1) (i j : Fin k) :
    dualSub Rg k (dualM Rg k i j) = (P _ k).det * (genM Rg k).det ^ (k - 2) * X (i, j) := by
  have h1 : dualSub Rg k (dualM Rg k i j) = adjugate (dualM Rg k) (Fin.rev j) i := by
    have e : (dualSub Rg k).toRingHom.mapMatrix (adjugate (genM Rg k)) (Fin.rev j) i =
        adjugate (dualM Rg k) (Fin.rev j) i := by
      rw [RingHom.map_adjugate, map_genM]
    rw [← e]; rfl
  have h2 : (adjugate (dualM Rg k))ᵀ * P _ k = ((P _ k).det * (genM Rg k).det ^ (k - 2)) • genM Rg k := by
    rw [dualM_eq, adjugate_mul_distrib, ← adjugate_transpose, adjugate_adjugate _ (by simpa using hk),
      Matrix.transpose_mul, Matrix.transpose_transpose, adjugate_transpose, P_transpose,
      Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, Fintype.card_fin]
  have h3 := congrArg (fun M => M i j) h2
  simp only [mul_P, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h3
  rw [h1, h3]; simp [genM]
end PI.OddDualWeyl.Uniq
