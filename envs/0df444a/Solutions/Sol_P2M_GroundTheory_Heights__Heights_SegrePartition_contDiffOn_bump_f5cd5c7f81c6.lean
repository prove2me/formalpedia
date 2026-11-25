-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_contDiffOn_bump_f5cd5c7f81c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:35.670549+00:00
-- url     : https://prove2.me/submissions/756b9e55-4c6f-4b4e-bb94-2326839eccc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSq_aac3f18011a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1


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
theorem _root_.solution (i : (k : K) → ι k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bump z i)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine (Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_
  refine ContDiffOn.sub (contDiffOn_const.mul ?_) contDiffOn_const
  exact ContDiffOn.div (contDiff_segreSq i).contDiffOn contDiff_segreSqSum.contDiffOn
    fun z hz => (segreSqSum_pos hz).ne'
end GroundTheory.Heights₂.Heights.SegrePartition
