-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_comm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:54.858717+00:00
-- url     : https://prove2.me/submissions/8c3ec6c5-69c1-4303-828f-d08e24c3365a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti

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
theorem _root_.solution {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ) (A : ι → R) (B : κ → R) :
    (∑ x ∈ s, A x) * (∑ y ∈ t, B y) - (∑ y ∈ t, B y) * (∑ x ∈ s, A x) =
      ∑ x ∈ s, ∑ y ∈ t, (A x * B y - B y * A x) := by
  have h1 : (∑ x ∈ s, A x) * (∑ y ∈ t, B y) = ∑ x ∈ s, ∑ y ∈ t, A x * B y := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  have h2 : (∑ y ∈ t, B y) * (∑ x ∈ s, A x) = ∑ x ∈ s, ∑ y ∈ t, B y * A x := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]; exact Finset.sum_comm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.DS
