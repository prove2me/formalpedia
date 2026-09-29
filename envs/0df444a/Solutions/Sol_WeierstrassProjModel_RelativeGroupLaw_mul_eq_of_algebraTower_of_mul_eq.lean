-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_algebraTower_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/24f9ebf5-56e9-53ef-804d-84d38e389f96

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (F : Type u) [Field F] [Algebra R F]
    (K : Type u) [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    (G₀ G₁ : WeierstrassProjModel.RelativeGroupLaw R f)
    (hK : ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f,
      G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
        = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by
  intro P Q

  set η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F K)) with hηdef

  have hη : η ≫ Spec.map (CommRingCat.ofHom (algebraMap R F))
      = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [hηdef, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  haveI : IsSchemeTheoreticallyDominant η := by
    have hsurj : Function.Surjective η.base := by
      intro x
      exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), Subsingleton.elim _ _⟩
    haveI : IsDominant η := ⟨hsurj.denseRange⟩
    exact (isSchemeTheoreticallyDominant_iff_isDominant η).mpr ‹_›

  have h0 := G₀.mul_natural
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) η hη P Q
  have h1 := G₁.mul_natural
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) η hη P Q

  have hcomp :
      schemeHomOverComp η hη (G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q)
        = schemeHomOverComp η hη (G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q) := by
    rw [h0, h1]
    exact hK (schemeHomOverComp η hη P) (schemeHomOverComp η hη Q)

  have hcomp1 :
      η ≫ (G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q).1
        = η ≫ (G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q).1 :=
    congrArg Subtype.val hcomp

  exact Subtype.ext
    (ext_of_isSchemeTheoreticallyDominant_of_isSeparated f
      ((G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q).2.trans
        (G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q).2.symm)
      η hcomp1)

end S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq (solution)
