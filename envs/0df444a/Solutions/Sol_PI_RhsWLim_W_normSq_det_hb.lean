-- Prove2me | solution 1 for PI.RhsWLim.W.normSq_det_hb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:39.971742+00:00
-- url     : https://prove2.me/submissions/441bd271-2443-48f3-8064-58844b641e44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution {k : ℕ} {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    Complex.normSq μ.det = 1 := by
  have h := congrArg Matrix.det hμ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hb : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> norm_num
  have h2 : star μ.det * μ.det = 1 := by
    have e : (star μ.det * μ.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [show (star μ.det * μ.det) * (Hb k).det = star μ.det * (Hb k).det * μ.det by ring, h, one_mul]
    exact mul_right_cancel₀ hb e
  have h3 : (Complex.normSq μ.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3
end PI.RhsWLim.W
