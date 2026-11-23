-- Prove2me | solution 1 for P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:11.904521+00:00
-- url     : https://prove2.me/submissions/802e50e2-cc6a-4611-bf5d-4f340c73381f

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
namespace GlobalTheory.AffineQuotient
theorem _root_.solution (U : Y.affineOpens) :
    (cover f g a ha p hp).f U ≫ fromQuot f g a ha p hp =
      Spec.map ((diagramMap f g a ha p hp).app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _
end GlobalTheory.AffineQuotient
