-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:04.046069+00:00
-- url     : https://prove2.me/submissions/b9c58d92-01c7-4aaf-8a27-87a14ea42f51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeSubvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace LocalizeSubvar
theorem _root_.solution {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (d : ℕ) (g : MvPolynomial σ R) :
    homogeneousComponent d (map f g) = map f (homogeneousComponent d g) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp
end LocalizeSubvar
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
