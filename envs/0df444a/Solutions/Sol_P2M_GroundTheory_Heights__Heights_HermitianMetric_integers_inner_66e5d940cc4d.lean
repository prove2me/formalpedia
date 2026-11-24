-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:15.90041+00:00
-- url     : https://prove2.me/submissions/440907e9-da53-4061-8e1a-8389b83f5f58

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
open ComplexAt
variable {K : Type*} [Field K]
attribute [instance] HermitianBundle.instAddCommGroup HermitianBundle.instModule
  HermitianBundle.instFinite HermitianBundle.instProjective
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace GroundTheory.Heights₂.Heights
namespace HermitianMetric
theorem _root_.solution (σ : K →+* ℂ) (z w : ComplexAt σ) (a b : 𝓞 K) :
    ((HermitianMetric.integers K).form σ).inner (z ⊗ₜ a) (w ⊗ₜ b) =
      starRingEnd ℂ (σ (a : K) * (ofComplex σ).symm z) * (σ (b : K) * (ofComplex σ).symm w) := by
  rw [mul_comm]; rfl
end HermitianMetric
end GroundTheory.Heights₂.Heights
