-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_headAdd_f9a6774e0aa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:27.793272+00:00
-- url     : https://prove2.me/submissions/e3fab88b-4143-418c-b0f3-cb3b39893c49

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0

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
theorem _root_.solution (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (Q : List (K → ℤ)) : HeadAdd (listNum W Q d) := by
  intro u v l
  unfold listNum
  simp only [List.length_cons, List.cons_append]
  split_ifs with h
  · exact vNumL_add_head h3 hϖ hP hD hW u v (l ++ Q) (by simp only [List.length_append]; omega)
  · simp
end GroundTheory.Heights₂.Heights.NumbersDVR
