-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:35.692951+00:00
-- url     : https://prove2.me/submissions/9fcac84e-f462-48a3-ba83-022c380fd090

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_comp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (h : Function.Surjective (algebraMap A B))
    (ω : KaehlerDifferential R K) :
    ω ∈ (KaehlerDifferential.map R R A K).range ↔
      ω ∈ (KaehlerDifferential.map R R B K).range := by
  constructor
  · rintro ⟨η,rfl⟩
    exact ⟨KaehlerDifferential.map R R A B η,(kaehler_field_map_comp R A B K η).symm⟩
  · rintro ⟨η,rfl⟩
    obtain ⟨ζ,rfl⟩ := KaehlerDifferential.map_surjective_of_surjective R R A B h η
    exact ⟨ζ,kaehler_field_map_comp R A B K ζ⟩
end QEC.Coding.AlgebraicGeometry
