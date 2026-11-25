-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:19.993738+00:00
-- url     : https://prove2.me/submissions/3fa576cb-8fe1-4a0a-b7ac-b3bd4dfff5c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
