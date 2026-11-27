-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:50.202157+00:00
-- url     : https://prove2.me/submissions/82d32d86-65ad-4b25-aab8-9a4ee771c52c

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
theorem _root_.solution (z : ComplexAt σ) : conjLinear σ z = conj σ z := rfl
end GroundTheory.Heights₂.Heights.ComplexAt
