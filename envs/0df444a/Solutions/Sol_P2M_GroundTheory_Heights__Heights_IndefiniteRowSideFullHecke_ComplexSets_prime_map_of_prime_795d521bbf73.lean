-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prime_map_of_prime_795d521bbf73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:24.638604+00:00
-- url     : https://prove2.me/submissions/b77906f9-e7e0-4390-835c-bdf47d9c6fc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (Ψ : R →+* S) {ω : R} (hω : Prime ω)
    (hne : Ψ ω ≠ 0) (hsurj : ∀ g : S, ∃ (Q : S) (p : R), g = Ψ ω * Q + Ψ p)
    (hdvd : ∀ p : R, Ψ ω ∣ Ψ p → ω ∣ p) : Prime (Ψ ω) := by
  refine ⟨hne, fun hu => hω.not_isUnit (isUnit_of_dvd_one (hdvd 1 (by rw [map_one]; exact hu.dvd))), ?_⟩
  intro g h hgh
  obtain ⟨Q₁, p₁, rfl⟩ := hsurj g
  obtain ⟨Q₂, p₂, rfl⟩ := hsurj h
  have h12 : Ψ ω ∣ Ψ (p₁ * p₂) := by
    have e : Ψ (p₁ * p₂) = (Ψ ω * Q₁ + Ψ p₁) * (Ψ ω * Q₂ + Ψ p₂) -
        Ψ ω * (Q₁ * (Ψ ω * Q₂ + Ψ p₂) + Ψ p₁ * Q₂) := by rw [map_mul]; ring
    rw [e]; exact dvd_sub hgh (dvd_mul_right _ _)
  rcases hω.dvd_or_dvd (hdvd _ h12) with h1 | h1
  · exact Or.inl (dvd_add (dvd_mul_right _ _) (map_dvd Ψ h1))
  · exact Or.inr (dvd_add (dvd_mul_right _ _) (map_dvd Ψ h1))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
