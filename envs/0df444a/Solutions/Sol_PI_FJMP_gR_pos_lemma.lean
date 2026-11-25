-- Prove2me | solution 1 for PI.FJMP.gR_pos_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:19.584832+00:00
-- url     : https://prove2.me/submissions/5ea847ba-697b-4893-ab13-6ecb6b06b01f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_pderiv_eq_zero_of_noVar
import Theorems.Thm_PI_FJMP_noVar_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
variable {κ : Type*} [Fintype κ]
namespace PI.FJMP
theorem _root_.solution (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = true → NoVar P (u c))
    (c0 : κ) (hc0 : pos c0 = true) : pderiv (v c0) P = 0 := by
  have hno0 := hno c0 hc0
  have key : ∀ a b, pderiv (u c0) (X a * pderiv b P) = pderiv b P * pderiv (u c0) (X a) := by
    intro a b
    rw [Derivation.leibniz, pderiv_eq_zero_of_noVar (noVar_pderiv hno0 b), smul_zero, zero_add, smul_eq_mul]
  have h0 : pderiv (u c0) (gR u v pos P) = 0 := by rw [hR, map_zero]
  unfold gR at h0
  rw [map_sum, Finset.sum_eq_single c0] at h0
  · rw [if_pos hc0, key, pderiv_X_self, mul_one] at h0
    exact h0
  · intro c _ hc
    split_ifs with hpc
    · rw [key, pderiv_X_of_ne (fun h => hc (hu h)), mul_zero]
    · rw [map_neg, key, pderiv_X_of_ne (huv c0 c).symm, mul_zero, neg_zero]
  · intro h
    exact absurd (Finset.mem_univ c0) h
end PI.FJMP
