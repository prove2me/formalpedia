-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_pow_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:46.622371+00:00
-- url     : https://prove2.me/submissions/ca1b8cb5-58ee-403d-96b8-7bd56c089b03

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
theorem _root_.solution {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℕ) :
    v (f ^ n) = ((n : ℤ) * m : ℤ) := by
  rw [v.map_pow,hf,← WithTop.coe_nsmul,nsmul_eq_mul]
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
