-- Prove2me | solution 1 for PI.RhsWLim.W.boost_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:31.87392+00:00
-- url     : https://prove2.me/submissions/5d21f45a-e1e6-42f5-a030-c017d14f1d59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_BallConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarDec

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
open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (y : Fin k → ℂ) (n : ℝ) (hn : 0 < n) : (boost y (n : ℂ))ᴴ = boost y (n : ℂ) := by
  have hnn : ‖(n : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  ext i j
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [boost]
    | cast j => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
    | cast j =>
      simp only [boost, Fin.lastCases_castSucc, hnn, map_add, map_div₀, map_mul, Complex.conj_conj,
        Complex.conj_ofReal, map_one]
      by_cases h : i = j
      · subst h; simp; ring
      · rw [if_neg (Ne.symm h), if_neg h]; simp; ring
end PI.RhsWLim.W
