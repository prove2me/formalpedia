-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_invOpen_mul_eq_inf_6088da3b938f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:27.960652+00:00
-- url     : https://prove2.me/submissions/6fd980c3-5311-4223-8b64-c1c74583c00c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7

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
theorem _root_.solution (f : X ⟶ SpecZ) (a b : ℤ) :
    invOpen f (a * b) = invOpen f a ⊓ invOpen f b := by
  ext x
  change a * b ∉ _ ↔ a ∉ _ ∧ b ∉ _
  exact mul_not_mem_prime_iff (PrimeSpectrum.isPrime _) a b
end GroundTheory.Heights₂.Heights.Model
