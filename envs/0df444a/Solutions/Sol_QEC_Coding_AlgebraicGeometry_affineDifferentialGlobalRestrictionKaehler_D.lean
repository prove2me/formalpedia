-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:50.421411+00:00
-- url     : https://prove2.me/submissions/c776c57e-4bbe-42f3-b4cf-23ab0e403571

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestriction_D
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalSectionsEquiv_D


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
local notation "f" => Spec.map q
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "cB" => affineDifferentialGlobalConstantMap k B
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k) cB
include hcoeff
variable [hopen : IsOpenImmersion (Spec.map q)]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (a : A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k B (q a) := by
  have h : (affineDifferentialGlobalSectionsEquiv k A).symm (KaehlerDifferential.D k A a) =
      (schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        ((Scheme.ΓSpecIso A).inv a) :=
    (affineDifferentialGlobalSectionsEquiv k A).symm_apply_eq.mpr
      (affineDifferentialGlobalSectionsEquiv_D k A a).symm
  change affineDifferentialGlobalSectionsEquiv k B
    (affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm (KaehlerDifferential.D k A a))) = _
  have h1 := congrArg (fun z : Γ(OmegaA, ⊤) =>
    affineDifferentialGlobalSectionsEquiv k B (affineDifferentialGlobalRestriction k A B q hcoeff z)) h
  have h2 := congrArg (fun z : Γ(OmegaB, ⊤) => affineDifferentialGlobalSectionsEquiv k B z)
    (affineDifferentialGlobalRestriction_D k A B q hcoeff a)
  exact h1.trans (h2.trans (affineDifferentialGlobalSectionsEquiv_D k B (q a)))
end QEC.Coding.AlgebraicGeometry
