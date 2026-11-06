-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_localization_clear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:39.078498+00:00
-- url     : https://prove2.me/submissions/6e30fcec-b069-4bf7-880c-a810c6507bb1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
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
theorem _root_.solution (S : Submonoid A) [IsLocalization S B]
    (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R B K).range) :
    ∃ s : S, s.val • omega ∈ (KaehlerDifferential.map R R A K).range := by
  rcases h with ⟨eta,rfl⟩
  obtain ⟨⟨tau,s⟩,he⟩ := IsLocalizedModule.surj S (KaehlerDifferential.map R R A B) eta
  change s.val • eta = KaehlerDifferential.map R R A B tau at he
  refine ⟨s,tau,?_⟩
  calc
    KaehlerDifferential.map R R A K tau =
        KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B tau) :=
      kaehler_field_map_comp R A B K tau
    _ = KaehlerDifferential.map R R B K (s.val • eta) := congrArg _ he.symm
    _ = s.val • KaehlerDifferential.map R R B K eta :=
      ((KaehlerDifferential.map R R B K).restrictScalars A).map_smul s.val eta
end QEC.Coding.AlgebraicGeometry
