-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_214e3020ee62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:52.106859+00:00
-- url     : https://prove2.me/submissions/fc8b8121-bf16-4bae-938b-b6a3f429b92f

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8


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
theorem _root_.solution (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  hUq F K ι I (isIntersectionTheory hPt hBase hI) V ((Objects.isMultiProjPrime_iff V).mpr hV.1) n
    (relDim_eq_of_ringKrullDim V n hV.2) L
end GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
