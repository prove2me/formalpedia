-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeGlueOverlap_image_intersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:23.349174+00:00
-- url     : https://prove2.me/submissions/3a3aebe0-bfac-4783-abcc-4c1ea8738f97

import Mathlib.AlgebraicGeometry.Gluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] QEC.Coding.AlgebraicGeometry.schemeGlueOverlapOpenImmersion
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (D : Scheme.GlueData.{u}) (i j : D.J) :
    (D.f i j ≫ D.ι i).opensRange = (D.ι i).opensRange ⊓ (D.ι j).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · exact ⟨D.f i j z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    · refine ⟨(D.t i j ≫ D.f j i) z, ?_⟩
      have h := congrArg (fun f => f z) (D.glue_condition i j)
      simpa only [Scheme.Hom.comp_apply] using h
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨z, hz, _⟩ := (D.ι_eq_iff i j a b).mp (ha.trans hb.symm)
    refine ⟨z, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ z).trans ((congrArg (D.ι i) hz).trans ha)
end QEC.Coding.AlgebraicGeometry
