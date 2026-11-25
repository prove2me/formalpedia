-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGramPosDef_proof_0c282fd0c601
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:53.763658+00:00
-- url     : https://prove2.me/submissions/2c94cfe8-3289-4639-bd59-020accb9cb7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramPosDef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50

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
open KLinesGramPosDef Matrix ComplexOrder
namespace GroundTheory.Heights₂.Heights
namespace LinesGramPosDef
theorem _root_.solution : LinesGramPosDef.Statement := by
  intro K _ n h σ ι _ u hh hu
  rw [gramAt_eq]
  exact hh.conjTranspose_mul_mul_same (mulVec_injective σ u hu)
end LinesGramPosDef
end GroundTheory.Heights₂.Heights
