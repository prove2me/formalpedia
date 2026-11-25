-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_commute_6f4d606e4172
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:39.766872+00:00
-- url     : https://prove2.me/submissions/531764f8-8884-4a77-8516-abe48d5f745f

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_cons_793b6e89e838

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
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (hC2 : VerticalDivisorsCommute.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g')
    (Q l : List (K → ℤ)) :
    cycEval (fun W => listNum W Q d (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => listNum W Q d (b :: l)) (ratDiv P f' g') := by
  unfold listNum
  simp only [List.length_cons, List.cons_append]
  by_cases h : l.length + 1 + Q.length = d
  · simp only [if_pos h]
    obtain rfl : d = (l ++ Q).length + 1 := by simp only [List.length_append]; omega
    simp only [vNumL_cons]
    exact hC2 O ϖ hϖ K ι P (l ++ Q).length hP b b' f g f' g' hD hD' (l ++ Q).get
  · simp [if_neg h, cycEval]
end GroundTheory.Heights₂.Heights.NumbersDVR
