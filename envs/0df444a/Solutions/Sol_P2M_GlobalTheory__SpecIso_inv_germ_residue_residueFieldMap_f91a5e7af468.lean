-- Prove2me | solution 1 for P2M_GlobalTheory__SpecIso_inv_germ_residue_residueFieldMap_f91a5e7af468
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:10.653891+00:00
-- url     : https://prove2.me/submissions/239089a1-607b-4b07-a3bb-e11f3eaa697d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R B : CommRingCat.{0}} (φ : R ⟶ B) (x : Spec B) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ x) trivial ≫
        (Spec R).residue (Spec.map φ x) ≫ (Spec.map φ).residueFieldMap x =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ x trivial ≫ (Spec B).residue x := by
  rw [Scheme.residue_residueFieldMap]
  erw [Scheme.Hom.germ_stalkMap_assoc (Spec.map φ) ⊤ x trivial]
  have hn := Scheme.ΓSpecIso_naturality φ
  rw [← Category.assoc, ← Category.assoc φ]
  congr 1
  show (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop = φ ≫ (Scheme.ΓSpecIso B).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
end GlobalTheory
