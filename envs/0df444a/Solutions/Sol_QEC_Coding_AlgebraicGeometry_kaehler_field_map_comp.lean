-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:47.222973+00:00
-- url     : https://prove2.me/submissions/c438df0c-d353-4731-be4d-3cec4ed36ce9

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (η : KaehlerDifferential R A) :
    KaehlerDifferential.map R R A K η =
      KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B η) := by
  have h : KaehlerDifferential.map R R A K =
      ((KaehlerDifferential.map R R B K).restrictScalars A).comp
        (KaehlerDifferential.map R R A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map R R A K (KaehlerDifferential.D R A a) =
      KaehlerDifferential.map R R B K
        (KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a))
    rw [KaehlerDifferential.map_D,KaehlerDifferential.map_D,KaehlerDifferential.map_D]
    exact congrArg (KaehlerDifferential.D R K) (IsScalarTower.algebraMap_apply A B K a)
  exact congrArg (fun f => f η) h
end QEC.Coding.AlgebraicGeometry
