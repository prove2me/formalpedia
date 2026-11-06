-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.valuation_eq_multiple_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:02:17.551754+00:00
-- url     : https://prove2.me/submissions/a09f74fc-c864-44ae-b463-42956fe0e522

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuationUnit_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_zpow_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
theorem _root_.solution [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ} (hm : v (π : K) = (m : WithTop ℤ))
    {f : K} (hf : f ≠ 0) : ∃ n : ℤ, v f = (n * m : ℤ) := by
  obtain ⟨n,u,he⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hf
  have he' : f = (u : V).val * (π.val ^ n) := by
    simpa only [Units.smul_def,Algebra.smul_def,ValuationSubring.algebraMap_apply] using he
  refine ⟨n,?_⟩
  rw [he',v.map_mul,valuationUnit_order v u,zero_add]
  exact valuation_zpow_finite v hm n
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
