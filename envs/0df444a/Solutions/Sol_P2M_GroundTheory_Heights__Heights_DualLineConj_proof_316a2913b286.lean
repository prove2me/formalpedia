-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineConj_proof_316a2913b286
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:55.401301+00:00
-- url     : https://prove2.me/submissions/1b563109-4f68-49cb-98af-a338c4912e7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DualLineConj
theorem _root_.solution : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]
end DualLineConj
end GroundTheory.Heights₂.Heights
