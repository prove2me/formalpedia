-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestriction_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:39.504933+00:00
-- url     : https://prove2.me/submissions/943133b0-edcb-4247-b507-fd38336e12d3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestrictionTo_D


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
    affineDifferentialGlobalRestriction k A B q hcoeff
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        (X := op ⊤) ((Scheme.ΓSpecIso A).inv a)) =
    (schemeDifferentialSheafDerivation (Spec B) (CommRingCat.of k) cB).d
      (X := op ⊤) ((Scheme.ΓSpecIso B).inv (q a)) := by
  have h1 := schemeDifferentialGlobalRestrictionTo_D (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff) ((Scheme.ΓSpecIso A).inv a)
  have hr := (congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => t a)
    (Scheme.ΓSpecIso_inv_naturality q)).symm
  have h2 := congrArg (fun b : Γ(Spec B, ⊤) =>
    (schemeDifferentialSheafDerivation (Spec B) (CommRingCat.of k) cB).d (X := op ⊤) b) hr
  exact h1.trans h2
end QEC.Coding.AlgebraicGeometry
