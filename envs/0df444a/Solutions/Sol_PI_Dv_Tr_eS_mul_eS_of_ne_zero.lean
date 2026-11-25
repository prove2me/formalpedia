-- Prove2me | solution 1 for PI.Dv.Tr.eS_mul_eS_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:08.770794+00:00
-- url     : https://prove2.me/submissions/fcbaca09-58b9-4cb3-828c-6652b32f0c80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_idem
import Theorems.Thm_PI_Dv_Tr_eS_ne_zero
import Theorems.Thm_PI_Dv_Tr_eS_mul_eS_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s t : T.S) (h : eS T s * eS T t ≠ 0) :
    eS T s * eS T t = eS T t := by
  obtain ⟨c, hc⟩ := eS_mul_eS_smul T s t
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact h hc
  have h2 : eS T s * (eS T s * eS T t) = eS T s * eS T t := by rw [← mul_assoc, eS_idem]
  rw [hc, mul_smul_comm, hc, smul_smul] at h2
  have h3 : (c * c - c) • eS T t = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have : c = 1 := by
      have : c * (c - 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hc0
      · linear_combination h5
    rw [hc, this, one_smul]
  · exact absurd h4 (eS_ne_zero T t)
end PI.Dv.Tr
