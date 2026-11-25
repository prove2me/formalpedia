-- Prove2me | solution 1 for PI.IsoInvMetricW.vnuMap_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:53.421234+00:00
-- url     : https://prove2.me/submissions/7e9d86fe-ba9e-4b4f-a364-540bf17c5fdb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
import Theorems.Thm_PI_IsoInvMetricW_metric_diagonal
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (z : ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu (fun s => Matrix.diagonal (dz z s)) φ I = z ^ wt I * φ I := by
  rw [vnuMap_eq]
  simp_rw [metric_diagonal Lt N nu (dz z), ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, dz, wt]
  simp_rw [Finset.prod_pow_eq_pow_sum]
end PI.IsoInvMetricW
