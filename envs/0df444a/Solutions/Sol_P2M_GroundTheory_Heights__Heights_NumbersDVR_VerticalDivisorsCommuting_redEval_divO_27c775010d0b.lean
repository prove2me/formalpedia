-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_redEval_divO_27c775010d0b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:13.676633+00:00
-- url     : https://prove2.me/submissions/a144f716-cf29-43dd-9445-b6811bbc9bb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WeilNumbersImpVerticalDivisorsCommute
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c


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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommuting
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommuting
theorem _root_.solution (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    IndefiniteRowSideFullHecke.NumbersDVR.redEval J (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
      cycEval (fun W => J (specialIdeal W)) (ratDiv P f g) := by
  rw [Objects.redEval_eq_cycEval]
  congr 1
  funext W
  exact Objects.divO_eq_ratDiv P f g W
end GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommuting
