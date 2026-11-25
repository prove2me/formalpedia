-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:18.320536+00:00
-- url     : https://prove2.me/submissions/f657f15f-5406-4d0f-9acf-109623df9ec3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ

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
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace FiniteIntegralClosure
theorem _root_.solution :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
      (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
      Module.Finite A (integralClosure A L)) ↔
    (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
      [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :=
  ⟨fun h A K L _ _ _ _ _ _ _ _ _ _ _ => h A K L, fun h A _ _ _ K _ _ _ L _ _ _ _ _ => h A K L⟩
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
