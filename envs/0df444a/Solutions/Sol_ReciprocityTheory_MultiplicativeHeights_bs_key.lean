-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bs_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:43:41.166851+00:00
-- url     : https://prove2.me/submissions/66e2fb62-7411-4271-ae0c-581b25aa3758

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BalancedSchwarz
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bs_mem_of_gauge_lt_one

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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ)
    (M : ℝ) (hs : IsOpen s) (hb : Balanced ℂ s) (hg : DifferentiableOn ℂ g s)
    (hM : ∀ w ∈ s, ‖g w‖ ≤ M) (h0 : (0 : E) ∈ s) (z : E) (R : ℝ) (hR : 1 < R)
    (hRt : R * gauge s z ≤ 1) : ‖g z - g 0‖ ≤ (M + ‖g 0‖) / R := by
  have hmaps : MapsTo (fun ζ : ℂ => ζ • z) (ball (0 : ℂ) R) s := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    apply bs_mem_of_gauge_lt_one hs hb h0
    rw [gauge_smul hb]
    calc ‖ζ‖ * gauge s z ≤ ‖ζ‖ * (1 / R) := by
          gcongr
          rw [le_div_iff₀ (by linarith)]; linarith
      _ < R * (1 / R) := by
          gcongr
      _ = 1 := by field_simp
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R) :=
    hg.comp (differentiableOn_id.smul_const z) hmaps
  have hm2 : MapsTo (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R)
      (closedBall ((fun ζ : ℂ => g (ζ • z)) 0) (M + ‖g 0‖)) := by
    intro ζ hζ
    simp only [zero_smul, mem_closedBall, dist_eq_norm]
    calc ‖g (ζ • z) - g 0‖ ≤ ‖g (ζ • z)‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ M + ‖g 0‖ := by gcongr; exact hM _ (hmaps hζ)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one]; exact hR
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm2 h1
  simpa [dist_eq_norm] using this
end ReciprocityTheory.MultiplicativeHeights
