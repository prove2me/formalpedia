-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_conjT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:12.525348+00:00
-- url     : https://prove2.me/submissions/05bee66c-4dd0-4076-9a7b-d86414bfa2c4

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
theorem _root_.solution {l m n : Type*} [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    ((M * N).map σ)ᵀ = (N.map σ)ᵀ * (M.map σ)ᵀ := by
  ext i j
  simp only [transpose_apply, map_apply, mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end PI.SqPair.LocCartanPairW
