-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:36.458244+00:00
-- url     : https://prove2.me/submissions/d1ab4b7b-b859-4c90-9bb2-ab890f051911

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_ExistsDominantSubSmul

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution (d : IndexData) (u w : Idx d → ℚ) (hu : IsRegular d (uR d u)) :
    ∃ s1 : ℝ, 0 < s1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s1 → IsDominant d (uR d (u - s • w)) := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
      0 < ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
    rw [Filter.eventually_all]; intro τ
    rw [Filter.eventually_all]; intro a
    rw [Filter.eventually_all]; intro b
    by_cases hab : b.val = a.val + 1
    · have hpos : (0 : ℝ) < (u (τ, a) : ℝ) - u (τ, b) := hu τ a b hab
      have hc : Continuous fun t : ℝ =>
          ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
        fun_prop
      have h0 : (0 : ℝ) <
          (fun t : ℝ => ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b))) 0 := by
        simpa using hpos
      filter_upwards [(hc.tendsto 0).eventually (lt_mem_nhds h0)] with t ht _ using ht
    · exact Filter.Eventually.of_forall fun _ h => absurd h hab
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, fun s hs hsle τ a b hab => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd : dist (s : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs']
    linarith
  have key := hball hd τ a b hab
  simp only [uR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  linarith
end GroundTheory.Heights₂.Heights.TheoremB
