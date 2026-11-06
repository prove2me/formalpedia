-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehlerLinear_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:06.066792+00:00
-- url     : https://prove2.me/submissions/49939d84-2faa-43df-9260-8e64b37e8686

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehler_D

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
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution :
    affineDifferentialGlobalRestrictionKaehlerLinear k A B q hcoeff hq =
      KaehlerDifferential.map k k A B := by
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation k A)
  intro a
  change affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (KaehlerDifferential.D k A a) =
    KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)
  exact (affineDifferentialGlobalRestrictionKaehler_D k A B q hcoeff a).trans
    ((congrArg (KaehlerDifferential.D k B) (hq a)).trans (KaehlerDifferential.map_D k k A B a).symm)
end QEC.Coding.AlgebraicGeometry
