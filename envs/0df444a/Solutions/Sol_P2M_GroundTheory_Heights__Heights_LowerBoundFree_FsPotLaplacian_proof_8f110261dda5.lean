-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FsPotLaplacian_proof_8f110261dda5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:31.774664+00:00
-- url     : https://prove2.me/submissions/7640e14f-4389-410c-9c9a-c4d1feba1443

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_integrable_laplacian_fsPotPlane_e519a5d24e07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_laplacian_fsPotPlane_570a8f9b2813

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
namespace FsPotLaplacian
theorem _root_.solution : FsPotLaplacian.Statement :=
  ⟨laplacian_fsPotPlane, integrable_laplacian_fsPotPlane, integral_laplacian_fsPotPlane⟩
end FsPotLaplacian
end GroundTheory.Heights₂.Heights.LowerBoundFree
