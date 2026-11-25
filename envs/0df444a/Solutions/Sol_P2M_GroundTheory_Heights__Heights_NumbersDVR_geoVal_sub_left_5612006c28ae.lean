-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_geoVal_sub_left_5612006c28ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:46:42.612161+00:00
-- url     : https://prove2.me/submissions/9bf8c0fe-487c-49a9-a90a-4be0ddd9907d

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_sub_f8bacce55cb1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_fun_sub_fde591e95c3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HeadAdd_sub_41ce92198c50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_sub_left_46d9475114cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb

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
theorem _root_.solution {A : List (K → ℤ) → ℤ} (hp : PermInv A) (ha : HeadAdd A) (k : ℕ)
    (a b c : K → ℤ) :
    geoVal A k a c - geoVal A k b c =
      polyVal (fun l => A ((a - b) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2)) := by
  have e1 : geoVal A k a c = polyVal A ![a, b, c] (geoSum k (X 0) (X 2)) :=
    (polyVal_geoSum_three A k a b c 0 2).symm
  have e2 : geoVal A k b c = polyVal A ![a, b, c] (geoSum k (X 1) (X 2)) :=
    (polyVal_geoSum_three A k a b c 1 2).symm
  rw [e1, e2, ← polyVal_sub, geoSum_sub_left, sub_mul, polyVal_sub, polyVal_X_mul hp,
    polyVal_X_mul hp, ← polyVal_fun_sub]
  congr 1
  funext l
  show A (a :: l) - A (b :: l) = A ((a - b) :: l)
  rw [ha.sub]
end GroundTheory.Heights₂.Heights.NumbersDVR
