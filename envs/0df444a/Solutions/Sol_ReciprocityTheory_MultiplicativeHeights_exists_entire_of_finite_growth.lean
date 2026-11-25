-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_entire_of_finite_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:55.971878+00:00
-- url     : https://prove2.me/submissions/e8787148-b20a-45c0-a422-c9f22f86a5ef

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Lemmata_IterateZero_IterZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_OnePolyGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Filter Topology Function Metric Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht
end ReciprocityTheory.MultiplicativeHeights
