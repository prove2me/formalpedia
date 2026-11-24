-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_rename_1c775c5899c9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.549859+00:00
-- url     : https://prove2.me/submissions/dc540419-2273-4813-8452-db7a8130b31e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_monomial_9bfc408d7757

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
variable {K : Type*} {σ τ : Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (A : List (K → ℤ) → ℤ) (cls : τ → K → ℤ) (ρ : σ → τ)
    (H : MvPolynomial σ ℤ) :
    polyVal A cls (rename ρ H) = polyVal A (cls ∘ ρ) H := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [rename_monomial, polyVal_monomial, polyVal_monomial]
    unfold classList
    rw [← Finsupp.toMultiset_map, Multiset.map_map]
  | add p q hp hq => rw [map_add, polyVal_add, polyVal_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR
