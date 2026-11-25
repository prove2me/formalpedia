-- Prove2me | solution 1 for PI.Mk.kron_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:47.838301+00:00
-- url     : https://prove2.me/submissions/5ad4f7e5-cd8f-4dbf-a2e0-3fd66aedfe43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset
namespace PI.Mk
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A B : Matrix n n ℤ) :
    kron k (A * B) = kron k A * kron k B := by
  ext i j
  simp only [kron, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.prod_mul_distrib]
end PI.Mk
