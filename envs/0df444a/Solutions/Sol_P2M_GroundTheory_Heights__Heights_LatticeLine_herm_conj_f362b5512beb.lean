-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:16.679343+00:00
-- url     : https://prove2.me/submissions/a3094b1a-b6fd-4544-8139-4888b9c84a20

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
namespace GroundTheory.Heights₂.Heights.LatticeLine
theorem _root_.solution (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (star (fun j ↦ starRingEnd ℂ (w j)) ⬝ᵥ
        (F.metric (ComplexEmbedding.conjugate s) *ᵥ fun j ↦ starRingEnd ℂ (w j))).re =
      (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by
  rw [F.conj s]
  have h : star (fun j ↦ starRingEnd ℂ (w j)) ⬝ᵥ ((F.metric s).map (starRingEnd ℂ) *ᵥ
      fun j ↦ starRingEnd ℂ (w j)) = starRingEnd ℂ (star w ⬝ᵥ (F.metric s *ᵥ w)) := by
    simp [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
  rw [h, Complex.conj_re]
end GroundTheory.Heights₂.Heights.LatticeLine
