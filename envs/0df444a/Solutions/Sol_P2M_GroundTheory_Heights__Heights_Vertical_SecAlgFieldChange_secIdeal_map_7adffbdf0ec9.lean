-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:39.779073+00:00
-- url     : https://prove2.me/submissions/fe6e433b-05a3-4575-95a2-bde2a23028fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
namespace GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e : ℕ}
    (Q₀ : Ideal (MvPolynomial (Fin n) R)) (y₀ : Par e n → R) :
    secIdeal (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀) =
      (secIdeal Q₀ y₀).map (MvPolynomial.map φ) := by
  have h1 : (MvPolynomial.map φ) ∘ secForm y₀ = secForm (φ ∘ y₀) := by
    funext i; simp [secForm, map_linForm]; rfl
  have h2 : MvPolynomial.map φ (chartForm y₀) = chartForm (φ ∘ y₀) := by
    simp [chartForm, map_linForm]; rfl
  simp only [secIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, map_one, h2,
    ← Set.range_comp, h1]
end GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
