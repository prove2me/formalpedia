-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:17.984916+00:00
-- url     : https://prove2.me/submissions/c347e120-709f-499d-9345-a91298aab03f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists

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
omit [NumberField K]
open Classical
namespace GroundTheory.Heights₂.Heights.LatticeLine
theorem _root_.solution
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s t : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    recover R t (latticePoint φ s w ()) = if t = s then w else 0 := by
  funext j
  have h1 : ∀ i, ∑ b, R t j b * (s (φ b i) * w i) = (if s = t ∧ i = j then 1 else 0) * w i := by
    intro i
    rw [← hR t j s i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  simp only [recover, latticePoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [h1]
  by_cases hts : t = s
  · subst hts
    simp
  · simp [hts, Ne.symm hts]
end GroundTheory.Heights₂.Heights.LatticeLine
