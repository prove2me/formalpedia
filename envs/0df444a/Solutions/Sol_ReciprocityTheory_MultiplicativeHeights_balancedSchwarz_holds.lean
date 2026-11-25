-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.balancedSchwarz_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:55:12.287034+00:00
-- url     : https://prove2.me/submissions/214adf92-d932-4dc2-8a84-8c2abd7c5cc3

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BalancedSchwarz
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bs_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Metric Set
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : BalancedSchwarzStatement := by
  intro E _ _ s g M hs hb hg hM z hz
  have h0 : (0 : E) ∈ s := by simpa using hb.smul_mem (a := (0 : ℂ)) (by simp) hz
  have ht0 : 0 ≤ gauge s z := gauge_nonneg z
  have ht1 : gauge s z < 1 := gauge_lt_one_of_mem_of_isOpen hs hz
  have hN : 0 ≤ M + ‖g 0‖ := by
    have := hM 0 h0; have := norm_nonneg (g 0); linarith
  rcases ht0.lt_or_eq with hpos | hzero
  · have := bs_key s g M hs hb hg hM h0 z (1 / gauge s z)
      (by rw [lt_div_iff₀ hpos]; linarith) (by field_simp; rfl)
    simpa [div_eq_mul_inv, mul_comm] using this
  · rw [← hzero, mul_zero]
    by_contra hne'
    have hne := not_le.mp hne'
    set d := ‖g z - g 0‖
    have hR : 1 < (M + ‖g 0‖) / d * 2 + 2 := by
      have : 0 ≤ (M + ‖g 0‖) / d * 2 := by positivity
      linarith
    have := bs_key s g M hs hb hg hM h0 z ((M + ‖g 0‖) / d * 2 + 2) hR
      (by rw [← hzero, mul_zero]; exact zero_le_one)
    rw [le_div_iff₀ (by linarith)] at this
    have h3 : d * ((M + ‖g 0‖) / d * 2 + 2) = 2 * (M + ‖g 0‖) + 2 * d := by
      field_simp
    nlinarith
end ReciprocityTheory.MultiplicativeHeights
