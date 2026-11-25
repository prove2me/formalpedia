-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_exists_bump_pos_3690f2e2b631
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:12.606453+00:00
-- url     : https://prove2.me/submissions/810fd4f0-f3a6-4f21-93ca-9e734cd66c17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegrePartition
theorem _root_.solution (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    ∃ j, 0 < bump z j := by
  by_contra h
  push Not at h
  have hle : ∀ j, segreSq z j ≤ segreSqSum z / (2 * numIdx ι) := by
    intro j
    have h1 : 2 * numIdx ι * (segreSq z j / segreSqSum z) - 1 ≤ 0 := by
      by_contra h2
      exact absurd (Real.smoothTransition.pos_of_pos (lt_of_not_ge h2)) (not_lt.mpr (h j))
    rw [le_div_iff₀ (by positivity)]
    have h3 : 2 * numIdx ι * segreSq z j / segreSqSum z ≤ 1 := by
      rw [mul_div_assoc]; linarith
    rw [div_le_one hS] at h3
    linarith
  have hsum : segreSqSum z ≤ numIdx ι * (segreSqSum z / (2 * numIdx ι)) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => segreSq z j) _ fun j _ => hle j
    rw [Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have h4 : numIdx ι * (segreSqSum z / (2 * numIdx ι)) = segreSqSum z / 2 := by
    field_simp
  linarith
end GroundTheory.Heights₂.Heights.SegrePartition
