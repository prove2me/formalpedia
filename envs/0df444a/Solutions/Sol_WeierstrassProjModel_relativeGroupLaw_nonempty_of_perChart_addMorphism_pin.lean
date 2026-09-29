-- Prove2me | solution 1 for WeierstrassProjModel.relativeGroupLaw_nonempty_of_perChart_addMorphism_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/10fc4e4c-92ff-544a-bcef-f969adf3b076

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_addMorphism_sixU_pin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_perChart_addMorphism_pin

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

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l) :
    Nonempty (WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective)) := by
  obtain ⟨m, hm_over, hm_chart⟩ :=
    WeierstrassProjModel.exists_addMorphism_of_perChart_addMorphism_pin W pcm hpin
  refine WeierstrassProjModel.relativeGroupLaw_nonempty_of_addMorphism_sixU_pin
    W m hm_over (fun i j l => ?_)

  refine .trans (congrArg (kw_lrSixU_locMap W i j l ≫ ·)
    ((Iso.inv_comp_eq (kwProjPullbackChartIsoCR R W.toProjective i j)).mpr
      (hm_chart (i, j)))) (hpin i j l)

end S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_perChart_addMorphism_pin
end P2MW
export P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_perChart_addMorphism_pin (solution)
