-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_pow_finite
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:15:05.426865+00:00
-- url     : https://prove2.me/submissions/998f05f9-14ec-4815-b606-41126547da61

-- ID: 30f15912-ae19-4ee9-bbc8-56e980d2e4a2 | NAME: QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_pow_finite | 未本地编译验证
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem solution {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℕ) :
    v (f ^ n) = ((n : ℤ) * m : ℤ) := by
  rw [AddValuation.map_pow, hf]
  change (↑(n • m) : WithTop ℤ) = ↑((n : ℤ) * m)
  rw [Int.nsmul_eq_mul]
