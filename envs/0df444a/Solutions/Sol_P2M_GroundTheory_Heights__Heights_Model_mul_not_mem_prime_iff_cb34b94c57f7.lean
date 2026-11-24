-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.71281+00:00
-- url     : https://prove2.me/submissions/f76db577-79e5-4abe-909d-4aab452575e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {P : Ideal ℤ} (hP : P.IsPrime) (a b : ℤ) :
    a * b ∉ P ↔ a ∉ P ∧ b ∉ P := by
  rw [hP.mul_mem_iff_mem_or_mem, not_or]
end GroundTheory.Heights₂.Heights.Model
