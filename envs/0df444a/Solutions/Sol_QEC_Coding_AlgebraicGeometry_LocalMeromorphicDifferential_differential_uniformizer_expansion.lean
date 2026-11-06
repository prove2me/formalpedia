-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.differential_uniformizer_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:31.723271+00:00
-- url     : https://prove2.me/submissions/f16b64de-4cfe-4444-9ede-092d764b7a5e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_22
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ∃ f : K, ω = f • KaehlerDifferential.D ℂ K (π : K) := by
  have hp : e (KaehlerDifferential.D ℂ K (π : K)) ≠ 0 := by
    intro hz
    exact uniformizerDifferential_ne_zero K a π m hm he
      (e.injective (hz.trans (map_zero e).symm))
  refine ⟨e ω / e (KaehlerDifferential.D ℂ K (π : K)),?_⟩
  apply e.injective
  rw [map_smul]
  exact (div_mul_cancel₀ (e ω) hp).symm
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
