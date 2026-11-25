-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isNormalScheme_specInt_f10714e7ae74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:44.43983+00:00
-- url     : https://prove2.me/submissions/83e52a64-10b9-47de-9a7a-566b2d7db17f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution : IsNormalScheme specInt where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have : x.asIdeal.IsPrime := x.isPrime
    let k : Algebra ℤ (specInt.presheaf.stalk x) := StructureSheaf.stalkAlgebra ℤ x
    have : IsLocalization.AtPrime (specInt.presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk ℤ x
    exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
