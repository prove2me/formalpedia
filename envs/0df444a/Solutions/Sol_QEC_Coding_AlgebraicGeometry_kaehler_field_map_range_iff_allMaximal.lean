-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff_allMaximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:03.649135+00:00
-- url     : https://prove2.me/submissions/68b5ac7c-ff34-4498-980d-b9ea9566c655

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_submodule_mem_of_forall_maximal_clear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_localization_clear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_comp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K]
variable (B : ∀ (P : Ideal A) [P.IsMaximal], Type*)
variable [∀ (P : Ideal A) [P.IsMaximal], CommRing (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (B P) P]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra R (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R (B P) K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (omega : KaehlerDifferential R K) :
    omega ∈ (KaehlerDifferential.map R R A K).range ↔
      ∀ (P : Ideal A) [P.IsMaximal], omega ∈ (KaehlerDifferential.map R R (B P) K).range := by
  constructor
  · rintro ⟨tau,rfl⟩ P hP
    exact ⟨KaehlerDifferential.map R R A (B P) tau,
      (kaehler_field_map_comp R A (B P) K tau).symm⟩
  · intro h
    apply submodule_mem_of_forall_maximal_clear A (KaehlerDifferential R K)
      (KaehlerDifferential.map R R A K).range omega
    intro P hP
    obtain ⟨s,hs⟩ := kaehler_field_map_range_localization_clear R A (B P) K
      P.primeCompl omega (h P)
    exact ⟨s.val,s.property,hs⟩
end QEC.Coding.AlgebraicGeometry
