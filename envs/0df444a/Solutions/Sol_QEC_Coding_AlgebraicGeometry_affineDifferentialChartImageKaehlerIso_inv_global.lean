-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_inv_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:20.800462+00:00
-- url     : https://prove2.me/submissions/df6f83fc-e764-40a8-bd95-4dbffc492985

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialImageSectionIsoTo_inv_global

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
theorem _root_.solution (s : Γ(OmegaX, ⊤)) :
    (affineDifferentialChartImageKaehlerIso k A f c hf).inv
      ((OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by
  change (affineDifferentialGlobalSectionsEquiv k A)
    ((schemeDifferentialRestrictionImageSectionIsoTo f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf ⊤).inv
        ((OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s)) =
    (affineDifferentialGlobalSectionsEquiv k A) ((psi) s)
  exact congrArg (affineDifferentialGlobalSectionsEquiv k A)
    (schemeDifferentialImageSectionIsoTo_inv_global f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf s)
end QEC.Coding.AlgebraicGeometry
