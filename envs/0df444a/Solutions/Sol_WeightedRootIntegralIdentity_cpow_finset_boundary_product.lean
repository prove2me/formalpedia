-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_finset_boundary_product
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T15:10:28.787082+00:00
-- url     : https://prove2.me/submissions/c6def98e-300c-4d76-ad5b-8147f197e298

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_negative_real_boundary
open scoped BigOperators

theorem solution
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f w : ι → ℝ)
    (hzero : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, ((f i : ℂ) ^ (w i : ℂ))) =
      ((∏ i ∈ s, Real.rpow |f i| (w i) : ℝ) : ℂ) *
        Complex.exp
          ((((Real.pi * (∑ i ∈ s.filter (fun j => f j < 0), w i) : ℝ) : ℝ) : ℂ) *
            Complex.I) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hx0 : f x ≠ 0 := hzero x (by simp)
      have hs0 : ∀ i ∈ s, f i ≠ 0 := by
        intro i hi
        exact hzero i (by simp [hi])
      have ihs := ih hs0
      by_cases hneg : f x < 0
      · have hsng :=
          (WeightedRootIntegralIdentity.cpow_negative_real_boundary
            (-f x) (w x) (by linarith)).1
        have hsng' :
            ((f x : ℂ) ^ (w x : ℂ)) =
              (Real.rpow |f x| (w x) : ℂ) *
                Complex.exp (((Real.pi * w x : ℝ) : ℂ) * Complex.I) := by
          convert hsng using 1 <;> simp [abs_of_neg hneg] <;> ring
        have hfilter :
            (insert x s).filter (fun j => f j < 0) =
              insert x (s.filter (fun j => f j < 0)) := by
          ext i
          by_cases hix : i = x
          · subst i
            simp [hneg, hx]
          · simp [hix]
        have hxfilter : x ∉ s.filter (fun j => f j < 0) := by
          simp [hx]
        rw [Finset.prod_insert hx, Finset.prod_insert hx, ihs, hsng',
          hfilter, Finset.sum_insert hxfilter]
        have harg :
            ((((Real.pi *
                (w x + ∑ i ∈ s.filter (fun j => f j < 0), w i) : ℝ) : ℝ) : ℂ) *
                Complex.I) =
              (((Real.pi * w x : ℝ) : ℂ) * Complex.I) +
              ((((Real.pi *
                (∑ i ∈ s.filter (fun j => f j < 0), w i) : ℝ) : ℝ) : ℂ) *
                Complex.I) := by
          push_cast
          ring
        rw [harg, Complex.exp_add]
        push_cast
        ring
      · have hnonneg : 0 ≤ f x := le_of_not_gt hneg
        have hsng' :
            ((f x : ℂ) ^ (w x : ℂ)) = (Real.rpow |f x| (w x) : ℂ) := by
          simpa [abs_of_nonneg hnonneg] using
            (Complex.ofReal_cpow hnonneg (w x)).symm
        have hfilter :
            (insert x s).filter (fun j => f j < 0) =
              s.filter (fun j => f j < 0) := by
          ext i
          by_cases hix : i = x
          · subst i
            simp [hneg, hx]
          · simp [hix]
        rw [Finset.prod_insert hx, Finset.prod_insert hx, ihs, hsng', hfilter]
        push_cast
        ring
