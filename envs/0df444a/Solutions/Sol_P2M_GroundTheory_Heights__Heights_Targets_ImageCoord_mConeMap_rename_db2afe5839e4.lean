-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:28.756316+00:00
-- url     : https://prove2.me/submissions/73e120fc-b100-48bb-93e2-8a29de0c9828

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageCoord

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Targets
namespace ImageCoord
theorem _root_.solution {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h
end ImageCoord
end GroundTheory.Heights₂.Heights.Targets
