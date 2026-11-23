-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_sum_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:35.622921+00:00
-- url     : https://prove2.me/submissions/48100dbc-16e1-42e4-a918-10c3f8572437

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ)
    (f : ι → κ → R) (X : R) (h : ∑ i ∈ s, ∑ c ∈ t, (f i c * X - X * f i c) = 0) :
    (∑ i ∈ s, ∑ c ∈ t, f i c) * X = X * ∑ i ∈ s, ∑ c ∈ t, f i c := by
  rw [← sub_eq_zero, ← h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.DS
