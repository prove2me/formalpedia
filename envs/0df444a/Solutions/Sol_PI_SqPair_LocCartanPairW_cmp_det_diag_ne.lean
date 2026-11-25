-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_det_diag_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:17.357416+00:00
-- url     : https://prove2.me/submissions/238185ea-1c0c-407a-aabc-09411ff02254

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [IsDomain R] {μ : Type*} [Fintype μ] [DecidableEq μ] (J : Matrix μ μ R)
    (hJ : J.det ≠ 0) (c : μ → R) (hc : ∀ i, c i ≠ 0) :
    (((diagonal c).map σ)ᵀ * J).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.diagonal_map (map_zero σ), Matrix.det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_) hJ
  intro h0
  exact hc i (σ.injective (by rw [h0, map_zero]))
end PI.SqPair.LocCartanPairW
