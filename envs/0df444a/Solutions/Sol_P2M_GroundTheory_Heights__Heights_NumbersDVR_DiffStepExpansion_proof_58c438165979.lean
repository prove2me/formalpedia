-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_proof_58c438165979
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:21.809738+00:00
-- url     : https://prove2.me/submissions/f3b16775-c692-404f-bee9-329a2ba75981

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDiffStepExpansion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
theorem _root_.solution : DiffStepExpansion.Statement := by
  intro K _ _ b
  have hb : b ∈ expandable K := by
    rw [← Finset.univ_sum_single b]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have : (Pi.single k (b k) : K → ℤ) = b k • (Pi.single k 1 : K → ℤ) := by
      ext j
      by_cases h : j = k <;> simp [h]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (single_mem k) _
  obtain ⟨l, hl⟩ := hb
  exact ⟨l, fun f => hl f⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
