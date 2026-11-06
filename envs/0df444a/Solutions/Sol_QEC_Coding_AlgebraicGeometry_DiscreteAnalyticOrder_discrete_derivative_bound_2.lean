-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.discrete_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:18:27.417198+00:00
-- url     : https://prove2.me/submissions/d1fee6d7-f1a7-403e-8a03-93c3cbec6e00

-- ID: 55198552-ebf4-4a71-8ba1-3ef7853c1949 | NAME: QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.discrete_derivative_bound | 未本地编译验证
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem solution {n m : ℤ} (hm : 0 < m) :
    0 ≤ n * m + (m - 1) ↔ 0 ≤ n * m := by
  constructor
  · intro h
    by_cases hn : 0 ≤ n
    · exact mul_nonneg hn (le_of_lt hm)
    · have hnle : n ≤ -1 := by omega
      have hmul : n * m ≤ (-1 : ℤ) * m := mul_le_mul_of_nonneg_right hnle (le_of_lt hm)
      nlinarith
  · intro h
    have hm1 : 0 ≤ m - 1 := by omega
    nlinarith
