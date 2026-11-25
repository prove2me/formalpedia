-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:41.454639+00:00
-- url     : https://prove2.me/submissions/0d32f658-0b5e-40fa-b5dc-32b80c06276d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution {J J' : Ideal (𝓞 K)} (h : J' ≤ J) (hn : Ideal.absNorm J' = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : J' = J := by
  obtain ⟨M, rfl⟩ := Ideal.dvd_iff_le.mpr h
  rw [map_mul] at hn
  have hM : Ideal.absNorm M = 1 := by
    have : Ideal.absNorm J * Ideal.absNorm M = Ideal.absNorm J * 1 := by rw [hn, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) this
  rw [Ideal.absNorm_eq_one_iff.mp hM, Ideal.mul_top]
end GroundTheory.Heights₂.Theta.ClassPeriodInv
