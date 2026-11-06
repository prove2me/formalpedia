-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.uniformizer_order_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:41.873028+00:00
-- url     : https://prove2.me/submissions/fc935f23-6937-4741-963d-369465fd6686

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
theorem _root_.solution (π : V) (hπ : Irreducible π) :
    0 < v (π : K) := by
  exact (Valuation.valuationSubring.integers (AddValuation.toValuation v)).valuation_irreducible_lt_one hπ
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
