-- Prove2me | solution 1 for PI.Mk.trace_kron
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:24.422594+00:00
-- url     : https://prove2.me/submissions/af57aa23-7b11-4b30-90f5-d33399ff9ab9

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A : Matrix n n ℤ) :
    (kron k A).trace = A.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, kron]
  rw [show (∑ i, A i i) ^ k = ∏ _t : Fin k, ∑ j, A j j by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    Finset.prod_univ_sum, Fintype.piFinset_univ]
end PI.Mk
