-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuationUnit_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:33.552187+00:00
-- url     : https://prove2.me/submissions/e895d6e2-1996-4a18-9f71-4cf0135c5f43

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
theorem _root_.solution (u : Vˣ) : v ((u : V) : K) = 0 := by
  exact (Valuation.valuationSubring.integers (AddValuation.toValuation v)).valuation_unit u
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
