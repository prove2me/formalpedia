-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_hyps_a74464e02c87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:53.334528+00:00
-- url     : https://prove2.me/submissions/4644921c-ab45-40c0-809a-71161597be81

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isFiniteTypeOverZ_specInt_2ea15994c44a

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
namespace FiniteIntegralClosure
theorem _root_.solution :
    (Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ) ∧
    (IsIntegral specInt ∧ IsFiniteTypeOverZ specInt ∧
      FiniteDimensional specInt.functionField specInt.functionField ∧
      IsAffineOpen (⊤ : specInt.Opens) ∧ Nonempty (⊤ : specInt.Opens)) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, isFiniteTypeOverZ_specInt, inferInstance, isAffineOpen_top _,
      ⟨⟨closedPt prime2, trivial⟩⟩⟩⟩
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
