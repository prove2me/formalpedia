-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEmbBijective_proof_80ddea4cacea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:57.440673+00:00
-- url     : https://prove2.me/submissions/8f8b6755-bf46-462b-b282-4908fa7cfe88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052

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
open NumberField Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DualEmbBijective
theorem _root_.solution : DualEmbBijective.Statement := by
  intro K _ _ i F T _ _ b
  have hinj := DualEmbeddingBijective.injective F b
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcard := DualEmbeddingBijective.card_le F b
  simp only [Module.finrank_fintype_fun_eq_card] at hle
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simp only [Module.finrank_fintype_fun_eq_card]
  omega
end DualEmbBijective
end GroundTheory.Heights₂.Heights
