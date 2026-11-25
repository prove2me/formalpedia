-- Prove2me | solution 1 for PI.RhsWLim.W.PH.lintegral_norm_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:18.921201+00:00
-- url     : https://prove2.me/submissions/63368da3-3661-43d7-a9c3-8b4083727152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
import Theorems.Thm_PI_RhsWLim_W_PH_lintegral_fun_norm
import Theorems.Thm_PI_RhsWLim_W_PH_finrank_ck

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
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH
namespace PI.RhsWLim.W.PH
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y : EuclideanSpace ℂ (Fin k), F ‖y‖ = ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial) *
      ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (2 * k - 1)) * F ρ := by
  have : Nontrivial (EuclideanSpace ℂ (Fin k)) := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    infer_instance
  rw [lintegral_fun_norm volume F hF, finrank_ck, Measure.toSphere_apply_univ, finrank_ck,
    InnerProductSpace.volume_ball, finrank_ck]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hG : Real.Gamma ((↑(2 * (n + 1)) : ℝ) / 2 + 1) = ((n + 1).factorial : ℝ) := by
    rw [show ((↑(2 * (n + 1)) : ℝ) / 2 + 1) = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [hG, ENNReal.ofReal_one, one_pow, one_mul, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [show ((↑(2 * (n + 1)) : ℝ≥0∞)) = ENNReal.ofReal ((2 * (n + 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp
  try ring
end PI.RhsWLim.W.PH
