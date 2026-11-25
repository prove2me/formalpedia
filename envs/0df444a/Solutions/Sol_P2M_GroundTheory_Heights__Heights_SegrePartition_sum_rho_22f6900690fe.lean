-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:21.734956+00:00
-- url     : https://prove2.me/submissions/1895b08c-bbfa-4f30-ae7b-74a9d893da45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_bump_sum_pos_2d44d42407bc

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
theorem _root_.solution (hN : 0 < numIdx ι) (z : (Σ k, ι k) → ℂ) : ∑ i, rho (ι := ι) i z = 1 := by
  by_cases hS : 0 < segreSqSum z
  · simp only [rho, if_pos hS]
    rw [← Finset.sum_div, div_self (bump_sum_pos hN hS).ne']
  · simp only [rho, if_neg hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [numIdx] at hN ⊢
    field_simp
end GroundTheory.Heights₂.Heights.SegrePartition
