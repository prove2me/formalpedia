-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:39.12948+00:00
-- url     : https://prove2.me/submissions/2039f0be-d3ef-4525-800a-3327db38f959

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R' : Type*} [CommRing R'] (φ : R →+* R')
    (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    (rabinowitschIdeal K g).map (MvPolynomial.map φ) =
      rabinowitschIdeal (K.map (MvPolynomial.map φ)) (MvPolynomial.map φ g) := by
  have h : (MvPolynomial.map φ).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (rename (R := R') (some : ι → Option ι)).toRingHom.comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => by simp [map_rename]
  simp only [rabinowitschIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, Set.image_singleton,
    map_sub, map_mul, map_one, map_X, h]
  simp [map_rename]
end GroundTheory.Heights₂.Heights
