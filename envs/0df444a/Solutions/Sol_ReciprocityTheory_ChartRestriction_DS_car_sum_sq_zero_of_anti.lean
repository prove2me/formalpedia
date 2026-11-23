-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_sum_sq_zero_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:36.260151+00:00
-- url     : https://prove2.me/submissions/f03addf2-d673-405c-a516-c4fbd1d9607e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem eq_zero_of_eq_neg_of_module_complex {M : Type*} [AddCommGroup M] [Module ℂ M] {v : M}
    (h : v = -v) : v = 0 := by
  have h3 : (2 : ℂ) • v = 0 := by
    rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
  calc v = (2 : ℂ)⁻¹ • ((2 : ℂ) • v) := by rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = 0 := by rw [h3, smul_zero]
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R ι : Type*} [Ring R] [Module ℂ R] (s : Finset ι) (F : ι → R)
    (h : ∀ x ∈ s, ∀ y ∈ s, F x * F y = -(F y * F x)) : (∑ x ∈ s, F x) * (∑ y ∈ s, F y) = 0 := by
  have e : (∑ x ∈ s, F x) * (∑ y ∈ s, F y) = ∑ x ∈ s, ∑ y ∈ s, F x * F y := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  have e2 : ∑ x ∈ s, ∑ y ∈ s, F x * F y = -∑ x ∈ s, ∑ y ∈ s, F x * F y := by
    calc ∑ x ∈ s, ∑ y ∈ s, F x * F y = ∑ x ∈ s, ∑ y ∈ s, -(F y * F x) :=
          Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => h x hx y hy
      _ = ∑ y ∈ s, ∑ x ∈ s, -(F y * F x) := Finset.sum_comm
      _ = -∑ y ∈ s, ∑ x ∈ s, F y * F x := by simp only [Finset.sum_neg_distrib]
  rw [e]
  exact eq_zero_of_eq_neg_of_module_complex e2
end ReciprocityTheory.ChartRestriction.DS
