-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntGramQf_proof_410c37431d3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:05.309374+00:00
-- url     : https://prove2.me/submissions/f0111ac4-c7a0-4af4-af6f-206ce8c24eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PIntGramQf

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace IntGramQf
theorem _root_.solution : IntGramQf.Statement := by
  intro d k S N z
  simp only [MCSchur.qf, intGram, ← mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]
end IntGramQf
end GroundTheory.Heights₂.Heights
