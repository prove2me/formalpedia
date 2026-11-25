-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_existsUnique_07925f7f61b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:58.842898+00:00
-- url     : https://prove2.me/submissions/b13a752f-4653-497d-8c42-780b2e246930

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumIsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_existsUnique_iff_a06986d0de6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_214e3020ee62

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
theorem _root_.solution (hN : Statement.{u}) (hUq : FieldNumbers.IntNumUnique.Statement.{u})
    (hPt : IntNumPoint.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u}) :
    ExistsUniqueStatement F ι :=
  (existsUnique_iff hN).mpr (agree hUq hPt hBase)
end GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
