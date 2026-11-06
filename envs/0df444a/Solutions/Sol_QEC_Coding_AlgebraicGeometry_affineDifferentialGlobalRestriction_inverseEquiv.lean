-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestriction_inverseEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:19.004242+00:00
-- url     : https://prove2.me/submissions/ab8ba930-85e4-4e5e-9179-fe51c7f9e303

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehler_eq_map

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
variable {X : Scheme.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k B)
include hq
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm s) =
    (affineDifferentialGlobalSectionsEquiv k B).symm
      (KaehlerDifferential.map k k A B s) := by
  apply (affineDifferentialGlobalSectionsEquiv k B).injective
  exact (affineDifferentialGlobalRestrictionKaehler_eq_map k A B q hcoeff hq s).trans
    ((affineDifferentialGlobalSectionsEquiv k B).apply_symm_apply _).symm
end QEC.Coding.AlgebraicGeometry
