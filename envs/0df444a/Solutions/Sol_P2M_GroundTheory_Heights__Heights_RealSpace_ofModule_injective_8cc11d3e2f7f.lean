-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:01.126801+00:00
-- url     : https://prove2.me/submissions/3917cceb-e595-444a-a918-30b48867b2f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K]
variable [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
variable (h : HermitianMetric K E)
open GroundTheory.Heights₂.Heights.RealSpace
namespace GroundTheory.Heights₂.Heights.RealSpace
theorem _root_.solution : Function.Injective (ofModule h) := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Free ℤ E := free_int K E
  set bZ := Module.finBasis ℤ E
  intro e e' he
  have h1 := congrArg (Algebra.TensorProduct.basis ℝ bZ).repr
    (show (1 : ℝ) ⊗ₜ[ℤ] e = (1 : ℝ) ⊗ₜ[ℤ] e' from he)
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul] at h1
  exact bZ.repr.injective
    (Finsupp.mapRange_injective _ _ (algebraMap ℤ ℝ).injective_int h1)
end GroundTheory.Heights₂.Heights.RealSpace
