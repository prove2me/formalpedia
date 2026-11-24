-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:08.12684+00:00
-- url     : https://prove2.me/submissions/d51d4e2b-666f-421b-aa56-0629ea2ab32d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution {R : Type*} [CommRing R] {σ τ M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : τ → N) (L : M →+ N)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ s, IsWeightedHomogeneous w' (φ (X s)) (L (w s)))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (φ f) (L m) := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, map_finsuppProd]
  have h1 : IsWeightedHomogeneous w' (d.prod fun s e => φ (X s ^ e)) (L m) := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    unfold Finsupp.prod
    refine IsWeightedHomogeneous.prod _ _ _ fun s _ => ?_
    show IsWeightedHomogeneous w' (φ (X s ^ d s)) (L (d s • w s))
    rw [map_pow, map_nsmul]
    exact (hφ s).pow _
  exact h1.C_mul _
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
