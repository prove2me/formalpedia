-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_ExactSequence_proof_60f4b6f79142
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:39.46266+00:00
-- url     : https://prove2.me/submissions/ed8d9e2b-870e-42ff-b4d9-7c3d282de074

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21


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
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.LatticeLemmas
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace ExactSequence
theorem _root_.solution : ExactSequence.Statement := by
  intro K _ _ M F hF
  simp only [HermitianBundle.deg]
  rw [(HermitianBundle.subQuotExtension M F hF).arithDegree_eq_add, add_div]
end ExactSequence
end GroundTheory.Heights₂.Heights.LatticeLemmas
