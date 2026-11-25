-- Prove2me | solution 1 for PI.FJMP.gR_neg_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:21.741997+00:00
-- url     : https://prove2.me/submissions/17cff2cb-81da-4624-b529-3bafc1e28f36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_gR_swap
import Theorems.Thm_PI_FJMP_gR_pos_lemma

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
theorem _root_.solution (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = false → NoVar P (v c))
    (c0 : κ) (hc0 : pos c0 = false) : pderiv (u c0) P = 0 := by
  have hR' : gR v u (fun c => !pos c) P = 0 := by rw [gR_swap, hR, neg_zero]
  exact gR_pos_lemma v u (fun c => !pos c) hv (fun c c' h => huv c' c h.symm) P hR'
    (fun c hc => hno c (by simpa using hc)) c0 (by simp [hc0])
end PI.FJMP
