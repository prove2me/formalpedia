-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ds_gen_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:22.154195+00:00
-- url     : https://prove2.me/submissions/ab6a0909-d6e9-470c-a894-798547e90ff1

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {S : Type*} [CommRing S] [IsLocalRing S] (A : Set S) (t : S)
    (ht0 : t ∈ nonZeroDivisors S) (hA : Ideal.span A = Ideal.span {t}) :
    ∃ y ∈ A, ∃ c : Sˣ, y = c * t := by
  by_contra hcon
  push_neg at hcon
  have hsub : Ideal.span A ≤ IsLocalRing.maximalIdeal S * Ideal.span {t} := by
    rw [Ideal.span_le]
    intro y hy
    have hyt : y ∈ Ideal.span {t} := by rw [← hA]; exact Ideal.subset_span hy
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hyt
    have hr' : r ∈ IsLocalRing.maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hcon y hy hu.unit (by rw [hu.unit_spec, hr])
    show y ∈ IsLocalRing.maximalIdeal S * Ideal.span {t}
    rw [← hr]
    exact Ideal.mul_mem_mul hr' (Ideal.mem_span_singleton_self t)
  have ht : t ∈ IsLocalRing.maximalIdeal S * Ideal.span {t} := by
    apply hsub; rw [hA]; exact Ideal.mem_span_singleton_self t
  obtain ⟨m, hm, hmt⟩ : ∃ m ∈ IsLocalRing.maximalIdeal S, m * t = t := by
    first
    | exact Ideal.mem_mul_span_singleton.mp ht
    | (obtain ⟨m, hm, hmt⟩ := Ideal.mem_span_singleton_mul.mp (by rwa [mul_comm] at ht)
       exact ⟨m, hm, by rw [mul_comm]; exact hmt⟩)
  have h1 : (1 - m) * t = 0 := by rw [sub_mul, one_mul, hmt, sub_self]
  have h2 : 1 - m = 0 := by
    first
    | exact (mul_right_mem_nonZeroDivisors_eq_zero_iff ht0).mp h1
    | exact (mul_cancel_right_mem_nonZeroDivisors ht0).mp (by rw [zero_mul]; exact h1)
    | exact (mem_nonZeroDivisors_iff.mp ht0).1 _ h1
    | exact mem_nonZeroDivisors_iff.mp ht0 _ h1
    | exact ht0.1 _ h1
    | exact ht0 _ h1
  have hm1 : m = 1 := (sub_eq_zero.mp h2).symm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hm1] at hm
  exact hm isUnit_one
end ReciprocityTheory.AnForm.R
