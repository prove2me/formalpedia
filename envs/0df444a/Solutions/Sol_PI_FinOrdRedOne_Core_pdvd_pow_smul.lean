-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:47.154614+00:00
-- url     : https://prove2.me/submissions/228d5957-e25d-4cdf-a75d-fba4efb162bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution (q : R) (a m : ℕ) (X : Matrix n n R) :
    PDvd q (a * m) ((q ^ a • X) ^ m) :=
  ⟨X ^ m, by rw [smul_pow, ← pow_mul]⟩
end PI.FinOrdRedOne.Core
