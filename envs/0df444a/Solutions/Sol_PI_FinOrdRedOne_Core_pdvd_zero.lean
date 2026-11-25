-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:51.155543+00:00
-- url     : https://prove2.me/submissions/dcbfdace-ce82-4188-becf-58515339e99a

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
theorem _root_.solution (q : R) (k : ℕ) : PDvd q k (0 : Matrix n n R) := ⟨0, by rw [smul_zero]⟩
end PI.FinOrdRedOne.Core
