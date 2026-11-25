-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:07.452673+00:00
-- url     : https://prove2.me/submissions/53f7c8b3-658d-41fd-bbd1-38a3ba361ad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_bump_sum_pos_2d44d42407bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_contDiffOn_bump_f5cd5c7f81c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d

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
theorem _root_.solution (hN : 0 < numIdx ι) (i : (k : K) → ι k) :
    IsDegZeroSmooth (rho (ι := ι) i) := by
  refine ⟨?_, fun c z hc => ?_⟩
  · have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (Σ k, ι k) → ℂ => bump z i / ∑ j, bump z j) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
      ContDiffOn.div (contDiffOn_bump i) (ContDiffOn.sum fun j _ => contDiffOn_bump j)
        fun z hz => (bump_sum_pos hN (segreSqSum_pos hz)).ne'
    refine hf.congr fun z hz => ?_
    simp only [rho, if_pos (segreSqSum_pos hz)]
  · have ha : 0 < ‖∏ k, c k‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)) 2
    have hS : 0 < segreSqSum (fun p => c p.1 * z p) ↔ 0 < segreSqSum z := by
      rw [segreSqSum_smul]; exact mul_pos_iff_of_pos_left ha
    simp only [rho, hS, bump_smul c z hc]
end GroundTheory.Heights₂.Heights.SegrePartition
