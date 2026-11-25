-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:30.881133+00:00
-- url     : https://prove2.me/submissions/2d0952d1-fe63-4869-afb7-8ed54127d113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7

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
theorem _root_.solution
    (h : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
      [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :
    ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  intro X _ hX L _ _ _ U hUa hU
  have := hU
  have := finiteType_sections_of_isFiniteTypeOverZ hX hUa
  have := functionField_isFractionRing_of_isAffineOpen X U hUa
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h Γ(X, U) X.functionField L
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
