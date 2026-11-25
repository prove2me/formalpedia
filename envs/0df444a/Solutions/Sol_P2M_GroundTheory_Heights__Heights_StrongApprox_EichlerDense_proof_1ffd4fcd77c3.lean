-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_proof_1ffd4fcd77c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:21.236209+00:00
-- url     : https://prove2.me/submissions/6faf7657-11a6-42de-a096-a35d224ba314

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace EichlerDense
theorem _root_.solution (h₁ : AETopologicalRing.Statement) (h₂ : EDenseInAE.Statement)
    (h₃ : OrthProjection.Statement) : EichlerDense.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ e f he hff hef _ _
  have hfe : hf c.toRingHom J f e = 1 :=
    hf_fe (fun x => EichlerDense.c_invol c h2 hc x) hJ he hff hef
  exact ⟨EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ e f he hff hef,
    EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ f e hff he hfe⟩
end EichlerDense
end GroundTheory.Heights₂.Heights.StrongApprox
