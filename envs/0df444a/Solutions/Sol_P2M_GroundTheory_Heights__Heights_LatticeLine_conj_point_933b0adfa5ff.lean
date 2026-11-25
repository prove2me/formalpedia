-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:14.543254+00:00
-- url     : https://prove2.me/submissions/b9325a64-4fcf-48d7-add0-ea96aa29a009

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
namespace GroundTheory.Heights₂.Heights.LatticeLine
theorem _root_.solution (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (fun b ↦ starRingEnd ℂ (latticePoint φ s w () b)) =
      latticePoint φ (ComplexEmbedding.conjugate s) (fun j ↦ starRingEnd ℂ (w j)) () := by
  funext b
  simp [latticePoint, ComplexEmbedding.conjugate_coe_eq, map_sum, map_mul]
end GroundTheory.Heights₂.Heights.LatticeLine
