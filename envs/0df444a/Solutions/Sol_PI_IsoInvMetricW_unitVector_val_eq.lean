-- Prove2me | solution 1 for PI.IsoInvMetricW.unitVector_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:20.301684+00:00
-- url     : https://prove2.me/submissions/db9acde2-37a3-4090-9ae7-620b88df831d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Theorems.Thm_PI_IsoInvMetricW_metric_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) :
    u0 N nu J = if J = J0 nu hle then 1 else 0 := by
  have e : u0 N nu J = E nu (fun _ => Matrix.diagonal (fun _ => (1 : ℂ))) J (J0 nu hle) := by
    unfold u0 hvC minY E
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    congr 1
    ext i k
    have hk : (k : ℕ) < N := lt_of_lt_of_le k.2
      (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))
    simp only [Matrix.of_apply, colsOf, hk, dite_true, Matrix.diagonal_one, J0]
    rfl
  rw [e, metric_diagonal]
  split_ifs <;> simp
end PI.IsoInvMetricW
