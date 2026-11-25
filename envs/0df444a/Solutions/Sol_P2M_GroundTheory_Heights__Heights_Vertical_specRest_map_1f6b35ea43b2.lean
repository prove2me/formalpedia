-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_specRest_map_1f6b35ea43b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:05.492803+00:00
-- url     : https://prove2.me/submissions/be626f8a-15f3-4faf-b244-eb1cb64d6d16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormForm

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
end GroundTheory.Heights₂.Heights.Vertical
