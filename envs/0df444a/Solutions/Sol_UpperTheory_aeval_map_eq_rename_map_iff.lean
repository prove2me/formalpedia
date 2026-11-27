-- Prove2me | solution 1 for UpperTheory.aeval_map_eq_rename_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:16.932841+00:00
-- url     : https://prove2.me/submissions/12e90ae1-beb6-4c08-88b6-ea773767e80c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightedHomogeneousMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by
  intro R S _ _ φ hφ σ M _ w ν f
  refine ⟨?_, ?_⟩
  · unfold MvPolynomial.IsWeightedHomogeneous
    refine forall_congr' fun d => ?_
    rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]
  · intro τ gR gS ρ hg
    have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
    subst hgS
    rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
      ← MvPolynomial.map_rename]
    exact (MvPolynomial.map_injective φ hφ).eq_iff
end UpperTheory
