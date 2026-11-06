-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:10.3632+00:00
-- url     : https://prove2.me/submissions/5dd905d5-3c52-424d-82c3-8490f23f8a55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehlerLinear_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)
include hq
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s =
      KaehlerDifferential.map k k A B s :=
  LinearMap.congr_fun
    (affineDifferentialGlobalRestrictionKaehlerLinear_eq k A B q hcoeff hq) s
end QEC.Coding.AlgebraicGeometry
