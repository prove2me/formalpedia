-- Prove2me | solution 1 for PositivityTheory.CW.casimir_real_of_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:39.328302+00:00
-- url     : https://prove2.me/submissions/48139a51-54bf-46db-8cdd-70e3abba1d47

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealOfCentral
import Theorems.Thm_PositivityTheory_CW_CasimirRealScalar_casimir_eq_trace
import Theorems.Thm_PositivityTheory_CW_CasimirRealScalar_cas_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A2 → A3 → CasimirIsRealScalar := by
  intro h2 h3
  unfold CasimirIsRealScalar ForMod
  intro n ε V _ _ E h
  have hc : ∀ a b, E a b * casimir E = casimir E * E a b := by
    intro a b
    rw [CasimirRealScalar.casimir_eq_trace]
    exact h2 n ε V E h 2 a b
  obtain ⟨c, hc'⟩ := h3 n ε V E h (casimir E) hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have him := CasimirRealScalar.cas_im ε E h.uni v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hcim : c.im = 0 := by
    rw [hc', inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.mul_im] at him
    have hre : ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have him2 : ((‖v‖ : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    erw [hre, him2, mul_zero, zero_add] at him
    rcases mul_eq_zero.mp him with h0 | h0
    · exact h0
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) hn
  refine ⟨c.re, fun w => ?_⟩
  rw [hc' w]
  congr 1
  apply Complex.ext <;> simp [hcim]
end PositivityTheory.CW
