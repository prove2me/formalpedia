-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionToKaehler_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:19.831381+00:00
-- url     : https://prove2.me/submissions/b1442e8b-e972-4d13-bdd2-504ca5fd795c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleSpecTop_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestrictionTo_smul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u})
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
attribute [local instance] QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalConstantModule
variable (A : CommRingCat.{u}) [Algebra k A] (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "psi" => schemeDifferentialGlobalRestrictionTo f (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) hf
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (r : k) (s : Γ(OmegaX, ⊤)) :
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf (r • s) =
      r • affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by
  change (affineDifferentialGlobalSectionsEquiv k A) ((psi) (c r • s)) =
    r • (affineDifferentialGlobalSectionsEquiv k A) ((psi) s)
  have hp := schemeDifferentialGlobalRestrictionTo_smul f (CommRingCat.of k) c
    (affineDifferentialGlobalConstantMap k A) hf (c r) s
  have hc : f.appTop (c r) = (Scheme.ΓSpecIso A).inv (algebraMap k A r) :=
    congrArg (fun t : CommRingCat.of k ⟶ Γ(Spec A, ⊤) => t r) hf
  have h1 := congrArg (affineDifferentialGlobalSectionsEquiv k A) hp
  have h2 := congrArg (fun b : Γ(Spec A, ⊤) =>
    (affineDifferentialGlobalSectionsEquiv k A) (b • (psi) s)) hc
  have h3 := congrArg (affineDifferentialGlobalSectionsEquiv k A)
    (schemeModuleSpecTop_smul A OmegaA (algebraMap k A r) ((psi) s)).symm
  have h4 := (affineDifferentialGlobalSectionsEquiv k A).map_smul (algebraMap k A r) ((psi) s)
  have h5 := IsScalarTower.algebraMap_smul A r
    ((affineDifferentialGlobalSectionsEquiv k A) ((psi) s))
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
end QEC.Coding.AlgebraicGeometry
