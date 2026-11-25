-- Prove2me | solution 1 for PI.RhsWLim.W.boost_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:28.84337+00:00
-- url     : https://prove2.me/submissions/0484cca9-a08a-4a59-8516-cf9a5fbda465

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
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
theorem _root_.solution (y : Fin k → ℂ) (c : ℂ)
    (hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1) (hc0 : c ≠ 0) :
    (boost y c)ᴴ * Hb k * boost y c = Hb k := by
  have hc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hD : (1 + ((‖c‖ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [norm_nonneg c]
  have hcc : conj c ≠ 0 := by rwa [map_ne_zero]
  have hn0 : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hc0
  have hcb : conj c = ((‖c‖ : ℝ) : ℂ) ^ 2 / c := by
    rw [eq_div_iff hc0]; exact hc
  ext i j
  rw [form_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_eq, if_true]
      rw [hS, hc]; ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j).symm]
      have h1 : ∀ l : Fin k, conj (y l) * ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = j then conj (y l) else 0) + (conj (y j) / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last i)]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) * y l =
          (if l = i then y l else 0) + (y i / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l
        simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        split_ifs <;> simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply, Fin.castSucc_inj,
        Fin.castSucc_ne_last, if_false]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) *
          ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = i then (if i = j then 1 else 0) else 0) + (if l = i then y i * conj (y j) / (1 + (‖c‖ : ℂ)) else 0) +
            (if l = j then conj (y l) * y i / (1 + (‖c‖ : ℂ)) else 0) +
            (y i * conj (y j) / (1 + (‖c‖ : ℂ)) ^ 2) * (conj (y l) * y l) := by
        intro l
        simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        by_cases hi : l = i <;> by_cases hj : l = j
        · subst hi; subst hj; simp <;> field_simp <;> ring
        · subst hi; simp [hj] <;> field_simp <;> ring
        · subst hj; simp [hi] <;> field_simp <;> ring
        · simp [hi, hj] <;> field_simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      split_ifs with hij
      · subst hij; try simp only [hcb]; field_simp; ring
      · try simp only [hcb]; field_simp; ring
end PI.RhsWLim.W
