-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:52.495607+00:00
-- url     : https://prove2.me/submissions/aa22878d-2395-4d9a-b342-c9e52250e67b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1

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
theorem _root_.solution {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < segreSqSum z := by
  choose i hi using hz
  have h : segre z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi k
  exact Finset.sum_pos' (fun j _ => segreSq_nonneg z j)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr h) 2⟩
end GroundTheory.Heights₂.Heights.SegrePartition
