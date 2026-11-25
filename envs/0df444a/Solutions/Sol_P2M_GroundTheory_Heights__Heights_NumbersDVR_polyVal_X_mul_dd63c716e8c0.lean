-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:16.743669+00:00
-- url     : https://prove2.me/submissions/c6d6c9dd-d269-46fc-880a-a9ee647006e9

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_341e4fbacfc8

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
theorem _root_.solution {A : List (K → ℤ) → ℤ} (hA : PermInv A) (cls : σ → K → ℤ) (s : σ)
    (H : MvPolynomial σ ℤ) :
    polyVal A cls (X s * H) = polyVal (fun l => A (cls s :: l)) cls H := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [X, monomial_mul, one_mul, polyVal_monomial, polyVal_monomial,
      hA _ _ (classList_single_add cls s μ)]
  | add p q hp hq => rw [mul_add, polyVal_add, polyVal_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR
