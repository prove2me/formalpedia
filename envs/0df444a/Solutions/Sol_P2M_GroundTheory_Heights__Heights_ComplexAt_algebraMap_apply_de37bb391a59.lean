-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:36.89406+00:00
-- url     : https://prove2.me/submissions/97f18581-de1a-4d6b-b270-5ad1bac6349e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)
namespace GroundTheory.Heights₂.Heights.ComplexAt
theorem _root_.solution (a : 𝓞 K) :
    algebraMap (𝓞 K) (ComplexAt σ) a = ofComplex σ (σ (a : K)) := rfl
end GroundTheory.Heights₂.Heights.ComplexAt
