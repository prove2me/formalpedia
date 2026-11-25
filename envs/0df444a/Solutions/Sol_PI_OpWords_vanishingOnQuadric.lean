-- Prove2me | solution 1 for PI.OpWords.vanishingOnQuadric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:14.928524+00:00
-- url     : https://prove2.me/submissions/0858002f-9a1c-4ec5-916d-a7b2093c3a67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
import Theorems.Thm_PI_OpWords_eval_eq_zero_of_support
import Theorems.Thm_PI_OpWords_xdeg_of_bihom
import Theorems.Thm_PI_OpWords_vanish_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution : Vanish := by
  intro K _ _ k d c W hW hst hwt hcd f hf p hp
  by_cases h : ∃ i0, p (Sum.inl i0) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    exact vanish_at W hW hst hwt hcd i0 Finset.univ p hi0 (fun b _ _ => Finset.mem_univ b) hp f hf
  · push_neg at h
    apply eval_eq_zero_of_support
    intro m hm
    have hsum := xdeg_of_bihom (hW hf) hm
    have hex : ∃ a, m (Sum.inl a) ≠ 0 := by
      by_contra h0
      push_neg at h0
      simp [h0] at hsum
      omega
    obtain ⟨a, ha⟩ := hex
    exact ⟨Sum.inl a, ha, h a⟩
end PI.OpWords
