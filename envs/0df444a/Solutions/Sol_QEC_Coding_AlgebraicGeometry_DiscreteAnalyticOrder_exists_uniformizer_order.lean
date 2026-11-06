-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.exists_uniformizer_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:21.757141+00:00
-- url     : https://prove2.me/submissions/880d6fb4-68ff-4ad4-889d-d6f2b3ea7a6b

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_uniformizer_order_positive

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
theorem _root_.solution [IsDiscreteValuationRing V] :
    ∃ (π : V) (m : ℤ), Irreducible π ∧ 0 < m ∧ v (π : K) = (m : WithTop ℤ) := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hne : v (π : K) ≠ ⊤ := v.ne_top_iff.mpr (by
    intro h
    exact hπ.ne_zero (Subtype.ext h))
  lift v (π : K) to ℤ using hne with m hm
  refine ⟨π,m,hπ,?_,hm.symm⟩
  have hp := uniformizer_order_positive v π hπ
  rw [← hm] at hp
  exact_mod_cast hp
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
