-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:11.839303+00:00
-- url     : https://prove2.me/submissions/750d0a49-a2a2-4624-b2cb-780fe327b285

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62

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
open NumberField Matrix
open scoped ComplexOrder ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLine
variable {K : Type} [Field K] [NumberField K] {r N : ℕ}
variable (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
  (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)
open Classical
namespace GroundTheory.Heights₂.Heights.LatticeLine
theorem _root_.solution
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    quad F φ R (latticePoint φ s w ()) = (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by
  have hrem : remainder φ R (latticePoint φ s w ()) = 0 := by
    funext b
    simp only [remainder, recover_point φ R hR, Pi.zero_apply]
    rw [Finset.sum_eq_single s (fun σ _ hσ ↦ by simp [hσ]) (fun h ↦ absurd (Finset.mem_univ s) h)]
    simp [latticePoint]
  simp only [quad, hrem, recover_point φ R hR, Pi.zero_apply, norm_zero]
  rw [Finset.sum_eq_single s (fun σ _ hσ ↦ by simp [hσ]) (fun h ↦ absurd (Finset.mem_univ s) h)]
  simp
end GroundTheory.Heights₂.Heights.LatticeLine
