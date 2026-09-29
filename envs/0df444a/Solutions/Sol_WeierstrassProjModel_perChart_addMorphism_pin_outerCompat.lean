-- Prove2me | solution 1 for WeierstrassProjModel.perChart_addMorphism_pin_outerCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9d165466-41d6-5a57-87dd-98fc5084d855

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_perChart_addMorphism_pin_over
import Theorems.Thm_WeierstrassProjModel_kw_pcmpin_outerCompat_dense_witness
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Limits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat

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
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "C9" => kwProjPullbackOpenCoverCR R W.toProjective

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij ij' : Fin 3 × Fin 3) :
    pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                 ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2
      = pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                     ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom ≫ pcm ij'.1 ij'.2 := by

  have h1 := perChart_addMorphism_pin_over W pcm hpin ij
  have h2 := perChart_addMorphism_pin_over W pcm hpin ij'
  have hover : (pullback.fst ((C9).f ij) ((C9).f ij')
          ≫ (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2) ≫ π
      = (pullback.snd ((C9).f ij) ((C9).f ij')
          ≫ (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom
          ≫ pcm ij'.1 ij'.2) ≫ π := by
    simp only [Category.assoc]
    refine (congrArg (pullback.fst ((C9).f ij) ((C9).f ij') ≫ ·) h1).trans ?_
    refine Eq.trans ?_ (congrArg (pullback.snd ((C9).f ij) ((C9).f ij') ≫ ·) h2.symm)
    exact pullback.condition_assoc _
  rcases isEmpty_or_nonempty ↥(pullback ((C9).f ij) ((C9).f ij')) with hV | hV
  · exact (isInitialOfIsEmpty (X := pullback ((C9).f ij) ((C9).f ij'))).hom_ext _ _
  · obtain ⟨D, ι, hdom, hagree⟩ :=
      kw_pcmpin_outerCompat_dense_witness W pcm hpin ij ij' hV
    haveI := hdom
    exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated (π) hover ι hagree

end

end S_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat
end P2MW
export P2MW.S_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat (solution)
