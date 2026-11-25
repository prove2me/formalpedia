-- Prove2me | solution 1 for PI.RhsWLim.W.col_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:26.616361+00:00
-- url     : https://prove2.me/submissions/54f14ed6-1c4d-4d50-8a64-7fbf5e97d4a7

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
import Theorems.Thm_PI_RhsWLim_W_form_apply


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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hμ : μᴴ * Hb k * μ = Hb k) (l : ℂ)
    (hl : conj l * l = 1) (hcol : ∀ i, μ i (Fin.last k) = if i = Fin.last k then l else 0) : μᴴ * μ = 1 := by
  have hl0 : conj l ≠ 0 := by intro h; rw [h, zero_mul] at hl; exact zero_ne_one hl
  have hrow : ∀ j, j ≠ Fin.last k → μ (Fin.last k) j = 0 := by
    intro j hj
    have h := congrFun (congrFun hμ (Fin.last k)) j
    rw [form_apply] at h
    simp only [hcol, Fin.castSucc_ne_last, if_false, map_zero, zero_mul, Finset.sum_const_zero, if_true,
      zero_sub, Hb, Matrix.diagonal_apply_ne _ (Ne.symm hj)] at h
    have : conj l * μ (Fin.last k) j = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left hl0
  have key : ∀ i j, (μᴴ * μ) i j = Hb k i j + 2 * (conj (μ (Fin.last k) i) * μ (Fin.last k) j) := by
    intro i j
    have h := congrFun (congrFun hμ i) j
    rw [form_apply] at h
    rw [← h, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  ext i j
  rw [key]
  by_cases hi : i = Fin.last k
  · by_cases hj : j = Fin.last k
    · subst hi; subst hj
      rw [hcol, if_pos rfl, hl]
      simp [Hb]; norm_num
    · rw [hrow j hj, mul_zero, mul_zero, add_zero, Hb, Matrix.diagonal_apply_ne _ (fun h => hj (h.symm.trans hi)),
        Matrix.one_apply_ne (fun h => hj (h.symm.trans hi))]
  · rw [hrow i hi, map_zero, zero_mul, mul_zero, add_zero, Hb, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; exact hi (h1 ▸ h2))
end PI.RhsWLim.W
