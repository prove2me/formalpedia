-- Prove2me | solution 1 for PI.OkpW.ultra_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:35.715151+00:00
-- url     : https://prove2.me/submissions/4adf875d-4671-49b8-a94d-6dd06edef197

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
namespace PI.OkpW
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x : ℕ → E) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) (k j : ℕ) :
    ‖x (j + k) - x k‖ ≤ r ^ (k + 1) := by
  induction j with
  | zero =>
    simp only [zero_add, sub_self, norm_zero]
    positivity
  | succ j ih =>
    have h1 := h (j + k)
    have h2 : ‖x (j + 1 + k) - x k‖ ≤ max ‖x (j + k + 1) - x (j + k)‖ ‖x (j + k) - x k‖ := by
      have h4 := IsUltrametricDist.norm_add_le_max (x (j + k + 1) - x (j + k)) (x (j + k) - x k)
      rw [show j + 1 + k = j + k + 1 by ring]
      simpa using h4
    have h3 : r ^ (j + k + 1) ≤ r ^ (k + 1) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    exact h2.trans (max_le (h1.trans h3) ih)
end PI.OkpW
