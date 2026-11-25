-- Prove2me | solution 1 for PI.SqPair.LCP.tau_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:03.549593+00:00
-- url     : https://prove2.me/submissions/a51fce60-47c5-4159-a713-2ba08252a0f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PlaneIsUnitOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP
open Polynomial IsLocalRing Matrix
namespace PI.SqPair.LCP
theorem _root_.solution {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x) (θ : R)
    (hθ : IsUnit (θ - σ θ)) : ∃ τ : R, τ + σ τ = 1 := by
  obtain ⟨u, hu⟩ := hθ
  refine ⟨θ * ↑u⁻¹, ?_⟩
  have hσu : σ (↑u : R) = -↑u := by rw [hu, map_sub, hσ]; ring
  have h2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hσinv : σ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : σ (↑u : R) * σ (↑u⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hσu] at h1
    linear_combination (-σ (↑u⁻¹ : R)) * h2 + (-(↑u⁻¹ : R)) * h1
  rw [map_mul, hσinv]
  rw [hu] at h2
  linear_combination h2
end PI.SqPair.LCP
