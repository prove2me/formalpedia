-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_uniformizer_derivative_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:03:12.015888+00:00
-- url     : https://prove2.me/submissions/d19e6fea-aea0-40f4-922c-a513d59d4ad4

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_eq_multiple_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_discrete_derivative_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
theorem _root_.solution [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ}
    (hpos : 0 < m) (hm : v (π : K) = (m : WithTop ℤ)) {f : K} (hf : f ≠ 0) :
    0 ≤ v f + ((m - 1 : ℤ) : WithTop ℤ) ↔ 0 ≤ v f := by
  obtain ⟨n,hn⟩ := valuation_eq_multiple_uniformizer v π hπ hm hf
  rw [hn,← WithTop.coe_add]
  exact_mod_cast discrete_derivative_bound (n := n) hpos
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
