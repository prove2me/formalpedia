-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockPoints_proof_635331ed52de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:45.929489+00:00
-- url     : https://prove2.me/submissions/3d49b9da-cab7-481a-a681-40753caa0ea5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace OneBlockPoints
theorem _root_.solution : OneBlockPoints.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨fun z hz ↦ ?_, fun σ w hw ↦ latticePoint_mem hφ σ hw, fun σ j₀ ↦ exists_left_inverse hφ σ j₀⟩
  obtain ⟨σ, w, hw, rfl⟩ := exists_latticePoint_eq hφ hz
  exact ⟨σ, ⟨w, hw, rfl⟩, fun σ' ⟨w', hw', h⟩ ↦ embedding_unique hφ hw' h.symm⟩
end OneBlockPoints
end GroundTheory.Heights₂.Heights
