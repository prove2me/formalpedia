-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:54.491881+00:00
-- url     : https://prove2.me/submissions/c60bfc95-11a1-4e37-93cc-aa5f8a3ee898

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_rename_1c775c5899c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab

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
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (A : List (K → ℤ) → ℤ) (k : ℕ) (a b c : K → ℤ) (i j : Fin 3) :
    polyVal A ![a, b, c] (geoSum k (X i) (X j)) = geoVal A k (![a, b, c] i) (![a, b, c] j) := by
  have e : (geoSum k (X i) (X j) : MvPolynomial (Fin 3) ℤ) =
      rename ![i, j] (geoSum k (X 0) (X 1)) := by
    rw [geoSum_rename]; rfl
  rw [e, polyVal_rename, geoVal]
  congr 1
  funext m
  fin_cases m <;> rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
