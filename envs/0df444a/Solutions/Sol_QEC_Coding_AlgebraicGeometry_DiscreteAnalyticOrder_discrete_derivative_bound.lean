-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.discrete_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:00.359981+00:00
-- url     : https://prove2.me/submissions/74a64ce7-ae4c-4b76-a639-7c708ecf543a

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
theorem _root_.solution {n m : ℤ} (hm : 0 < m) :
    0 ≤ n * m + (m - 1) ↔ 0 ≤ n * m := by
  constructor
  · intro h
    by_contra hn
    have hn' : n ≤ -1 := by
      by_contra hnn
      have h0 : 0 ≤ n := by omega
      exact hn (mul_nonneg h0 hm.le)
    have hp : n * m ≤ -m := by nlinarith
    omega
  · intro h
    have h1 : 1 ≤ m := by omega
    omega
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
