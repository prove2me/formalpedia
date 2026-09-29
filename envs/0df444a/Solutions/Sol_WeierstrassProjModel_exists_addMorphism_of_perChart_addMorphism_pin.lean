-- Prove2me | solution 1 for WeierstrassProjModel.exists_addMorphism_of_perChart_addMorphism_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e6202677-53fe-5a96-bc22-ac1bd95a8788

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat
import Theorems.Thm_WeierstrassProjModel_perChart_addMorphism_pin_over
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l) :
    ∃ (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
      (_ : m ≫ projModelStrCR W.toProjective
            = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective),
      ∀ (ij : Fin 3 × Fin 3),
        (kwProjPullbackOpenCoverCR R W.toProjective).f ij ≫ m
          = (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
              ≫ pcm ij.1 ij.2 := by
  let ψ : ∀ ij : Fin 3 × Fin 3,
      (kwProjPullbackOpenCoverCR R W.toProjective).X ij ⟶ E :=
    fun ij => (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2
  have hcompat := perChart_addMorphism_pin_outerCompat W pcm hpin
  refine ⟨(kwProjPullbackOpenCoverCR R W.toProjective).glueMorphisms ψ hcompat, ?_,
    fun ij => (kwProjPullbackOpenCoverCR R W.toProjective).ι_glueMorphisms ψ hcompat ij⟩
  refine (kwProjPullbackOpenCoverCR R W.toProjective).hom_ext _ _ (fun ij => ?_)
  rw [← Category.assoc,
    (kwProjPullbackOpenCoverCR R W.toProjective).ι_glueMorphisms ψ hcompat ij,
    ← Category.assoc]
  exact (Category.assoc _ _ _).trans (perChart_addMorphism_pin_over W pcm hpin ij)

end

end S_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin
end P2MW
export P2MW.S_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin (solution)
