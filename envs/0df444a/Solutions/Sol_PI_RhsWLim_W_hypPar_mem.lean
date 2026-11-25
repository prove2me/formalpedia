-- Prove2me | solution 1 for PI.RhsWLim.W.hypPar_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:53.232559+00:00
-- url     : https://prove2.me/submissions/98463583-9fa9-4b6f-bddb-b6eb0980a426

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Theorems.Thm_PI_RhsWLim_W_normSq_sum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (T' : ℝ) (hT' : 0 < T') (q : EuclideanSpace ℂ (Fin k) × ℝ) :
    hypPar k T' q ∈ hypS k T' := by

  have h1 : Complex.normSq (Complex.exp (q.2 * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  simp only [hypS, hypPar, Set.mem_setOf_eq]
  rw [normSq_sum_eq, Complex.normSq_mul, Complex.normSq_ofReal, h1, mul_one,
    Real.mul_self_sqrt (by positivity)]
  ring
end PI.RhsWLim.W
