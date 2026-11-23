-- Prove2me | solution 1 for P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:12.108584+00:00
-- url     : https://prove2.me/submissions/9f456510-e95c-48f6-b5e0-3367754333de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace GlobalTheory.AffineQuotient
theorem _root_.solution (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toQuot f g a ha p hp = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype) ≫
        (cover f g a ha p hp).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toQuot f g a ha p hp
  · congr 1; simp
  delta toQuot
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _
end GlobalTheory.AffineQuotient
