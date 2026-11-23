-- Prove2me | solution 1 for PI.SqfRootsInj.W.lp_pow_four_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:32.304392+00:00
-- url     : https://prove2.me/submissions/bc89d12e-c093-4827-b478-c45b4fad60ce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {g r e ℓ : ℕ} (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (h1 : 1 ≤ e)
    (h2 : e ≤ r) : (Lp g e ℓ) ^ 4 ≤ g ^ e := by
  by_contra h
  push_neg at h
  apply hB
  right
  refine ⟨e, h1, h2, hℓ, ?_⟩
  unfold Lp at h
  rwa [← pow_mul, mul_comm] at h
end PI.SqfRootsInj.W
