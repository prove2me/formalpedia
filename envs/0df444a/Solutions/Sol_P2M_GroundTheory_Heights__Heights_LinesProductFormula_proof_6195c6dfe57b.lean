-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesProductFormula_proof_6195c6dfe57b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:50.462684+00:00
-- url     : https://prove2.me/submissions/1a1a71ba-40f1-45aa-b85d-436bb375d6b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProductFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7

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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LinesProductFormula
theorem _root_.solution : LinesProductFormula.Statement := by
  intro K _ _ x hx
  rw [← KLinesProductFormula.prod_norm_embeddings K x, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)
end LinesProductFormula
end GroundTheory.Heights₂.Heights
