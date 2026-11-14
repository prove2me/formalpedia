-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_perturbation_dirac_zero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.362193+00:00
-- url     : https://prove2.me/submissions/4665f8e4-d66e-45f3-840f-847901a3d085

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d : ℕ) (hπ : ∀ a, m.pi t a ≠ 0) :
    (∀ a, Mmul m t (m.pi t) a = 1) ∧
    (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
      ∂((diracPi m t : ProbabilityMeasure (m.Spin → ℝ)) : Measure (m.Spin → ℝ)) = 0 := by
  classical
  have hrow (a : m.Spin) : Mmul m t (m.pi t) a = 1 := by
    unfold Mmul Model.M
    have heach (j : m.Spin) :
        m.P t a j / (m.pi t a * m.pi t j) * m.pi t j = m.P t a j / m.pi t a := by
      field_simp [hπ a,hπ j]
    simp_rw [heach, ← Finset.sum_div]
    change (m.pi t a) / (m.pi t a) = 1
    exact div_self (hπ a)
  refine ⟨hrow,?_⟩
  change (d:ℝ) * (∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2) ∂Measure.dirac (m.pi t)) = 0
  rw [MeasureTheory.integral_dirac]
  simp [hrow]
