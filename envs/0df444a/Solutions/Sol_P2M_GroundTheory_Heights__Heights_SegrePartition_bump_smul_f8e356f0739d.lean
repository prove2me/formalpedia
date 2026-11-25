-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:15.73158+00:00
-- url     : https://prove2.me/submissions/b9b54681-70c8-4532-a3a2-ff82c406321d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70

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
theorem _root_.solution (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (i : (k : K) → ι k) :
    bump (fun p => c p.1 * z p) i = bump z i := by
  have ha : ‖∏ k, c k‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))
  simp only [bump, segreSq_smul, segreSqSum_smul, mul_div_mul_left _ _ ha]
end GroundTheory.Heights₂.Heights.SegrePartition
