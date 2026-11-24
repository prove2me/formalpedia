-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ColonMultiHomog_proof_89514dc80a8c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:38.818606+00:00
-- url     : https://prove2.me/submissions/1f5fa889-e0ac-4f60-9565-b7b6353cb13b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ColonMultiHomog
theorem _root_.solution : ColonMultiHomog.Statement := by
  intro R _ K _ ι I f s hI hf y hy b
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy ⊢
  rw [component_mul_multiHomog y f b s hf]
  exact hI _ hy _
end ColonMultiHomog
end GroundTheory.Heights₂.Heights.NumbersDVR
