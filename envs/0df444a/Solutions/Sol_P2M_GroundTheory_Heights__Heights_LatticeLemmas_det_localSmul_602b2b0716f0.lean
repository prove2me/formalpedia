-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_localSmul_602b2b0716f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:14.806961+00:00
-- url     : https://prove2.me/submissions/dbbbeaf7-c2f9-4a2b-b778-778f1d2dd2b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      localScalar v b ^ Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] V) := by
  have : ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      localScalar v b • LinearMap.id := LinearMap.ext fun _ ↦ rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
end GroundTheory.Heights₂.Heights.LatticeLemmas
