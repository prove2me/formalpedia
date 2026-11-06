-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_zpow_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:27.711852+00:00
-- url     : https://prove2.me/submissions/4f5eb9ea-27e3-4242-9775-11bbb26c5674

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_pow_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
theorem _root_.solution {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℤ) :
    v (f ^ n) = (n * m : ℤ) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using valuation_pow_finite v hf n
  | negSucc n =>
      rw [zpow_negSucc,v.map_inv,valuation_pow_finite v hf]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr 1
      simp only [Int.negSucc_eq,Int.natCast_add,Int.natCast_one]
      ring
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
