-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:19.238358+00:00
-- url     : https://prove2.me/submissions/70d3a70c-ec44-4c68-b78f-36a4e90f4dac

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_proof_2e980415e0ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_214e3020ee62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumUnique_proof_a93d885aebf6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumIsFieldIntersection_proof_69885316002f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumRatSection_proof_1f2dabfb1efd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabDivCycle_proof_3cb2a32c78c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomogIdeal_proof_6afd59a7e16a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37


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
theorem _root_.solution (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  agree (FieldNumbers.IntNumUnique.proof hCut hBase hEx hDiv) (IntNumPoint.proof hBase) hBase I hI
    V n L hV
end GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
