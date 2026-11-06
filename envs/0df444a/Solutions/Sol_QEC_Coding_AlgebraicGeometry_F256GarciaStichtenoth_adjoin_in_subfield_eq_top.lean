-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_in_subfield_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:10:10.307446+00:00
-- url     : https://prove2.me/submissions/bc5240f4-9e2b-4588-bfae-363af48fb9fb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
    (K L : IntermediateField F E) [Fact (K ≤ L)]
    (z : E) (hz : z ∈ L) (hL : (K⟮z⟯).restrictScalars F = L) :
    K⟮(⟨z, hz⟩ : L)⟯ = ⊤ := by
  let f : L →ₐ[K] E := IsScalarTower.toAlgHom K L E
  apply IntermediateField.map_injective f
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map]
  apply IntermediateField.restrictScalars_injective F
  change (K⟮z⟯).restrictScalars F = f.fieldRange.restrictScalars F
  rw [hL]
  ext x
  change x ∈ L ↔ ∃ y : L, (y : E) = x
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
