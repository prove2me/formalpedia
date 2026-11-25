-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ds_prod_embeddings_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:02:05.203809+00:00
-- url     : https://prove2.me/submissions/ee4d2cb4-e77d-4355-a1b4-09a52cb56f46

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])
end ReciprocityTheory.GeometryOfNumbersTheory
