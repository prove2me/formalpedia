-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:38.638717+00:00
-- url     : https://prove2.me/submissions/1c28cef8-1062-4127-a344-bd01e9d6692f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he, Finset.sum_image]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [coeff_rename_mapDomain e he]
    congr 2
    unfold classList
    rw [← Finsupp.toMultiset_map, Multiset.map_map]
  · intro a _ b _ h
    exact Finsupp.mapDomain_injective he h
end GroundTheory.Heights₂.Heights.NumbersDVR
