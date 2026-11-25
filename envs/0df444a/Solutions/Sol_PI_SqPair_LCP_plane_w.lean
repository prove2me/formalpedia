-- Prove2me | solution 1 for PI.SqPair.LCP.plane_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:37.672801+00:00
-- url     : https://prove2.me/submissions/e5a430b9-38ca-4902-a668-a174deeada89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PlaneIsUnitOfSubOneMem
import Theorems.Thm_PI_SqPair_LCP_plane_core
import Theorems.Thm_PI_SqPair_LCP_plane_exists

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
theorem _root_.solution {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      (w.map σ)ᵀ * !![(α : R), 1; 1, (β : R)] * w = !![0, 1; 1, 0] ∧ ∃ s', w 1 0 = (α : R) * s' := by
  obtain ⟨t, s, c, h1, h2, h3, s', hs'⟩ := plane_exists σ hσ R₀ hR₀ τ hτ α β hα
  obtain ⟨hform, hdet⟩ := plane_core σ (α : R) (β : R) t s c ((hR₀ _).1 α.2) h1 h2 h3
  refine ⟨!![1 + s * t, c * t; s, c], ?_, hform, s', ?_⟩
  · rw [hdet]
    exact IsUnit.of_mul_eq_one _ h3
  · simp [hs']
end PI.SqPair.LCP
