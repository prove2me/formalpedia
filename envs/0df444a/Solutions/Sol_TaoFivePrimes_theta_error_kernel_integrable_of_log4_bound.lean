-- Prove2me | solution 1 for TaoFivePrimes.theta_error_kernel_integrable_of_log4_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:41:11.099012+00:00
-- url     : https://prove2.me/submissions/aba09b53-1a0e-420e-a52d-f4de07c5e448

import Mathlib
open MeasureTheory Filter Set
open scoped Topology

private theorem majorant_integrable (x : ℝ) (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => 100 * (Real.log t + 1) / (t * (Real.log t) ^ 6)) (Ioi x) := by
  let g : ℝ → ℝ := fun t => -(25 / (Real.log t) ^ 4 + 20 / (Real.log t) ^ 5)
  let d : ℝ → ℝ := fun t => 100 * (Real.log t + 1) / (t * (Real.log t) ^ 6)
  have hd : ∀ t ∈ Ici x, HasDerivAt g (d t) t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_of_lt_of_le hx ht)
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (lt_of_lt_of_le hx ht))
    have h4 := (hasDerivAt_const t (25 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 4) (pow_ne_zero 4 hl)
    have h5 := (hasDerivAt_const t (20 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 5) (pow_ne_zero 5 hl)
    convert (h4.add h5).neg using 1 <;> (try rfl) <;> (try dsimp [g, d]) <;>
      field_simp [htpos.ne', hl] <;> ring
  have hdpos : ∀ t ∈ Ioi x, 0 ≤ d t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_trans hx ht)
    have hl : 0 < Real.log t := Real.log_pos (lt_trans hx ht)
    dsimp [d]
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hh := ((hi.pow 4).const_mul 25 |>.add ((hi.pow 5).const_mul 20)).neg
    simpa [g, div_eq_mul_inv, inv_pow] using hh
  have hdi : IntegrableOn d (Ioi x) := integrableOn_Ioi_deriv_of_nonneg' hd hdpos hlim
  exact hdi

theorem solution
    (hθ : ∀ t : ℝ, 70111 ≤ t →
      |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t| ≤
        100 * t / (Real.log t) ^ 4) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) := by
  let θ : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)
  let R : ℝ → ℝ := fun t => (θ t - t) * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let g : ℝ → ℝ := fun t => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hθmeas : Measurable θ := (measurable_of_countable (fun n : ℕ => ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ))).comp Nat.measurable_floor
  have hRmeas : Measurable R := by dsimp [R]; fun_prop
  have hlocal : IntegrableOn R (Icc 2 70111) := by
    have hlogc : ContinuousOn (fun t : ℝ => Real.log t) (Icc (2 : ℝ) 70111) :=
      continuousOn_id.log (fun t ht => by change t ≠ 0; linarith [ht.1])
    have hg : ContinuousOn g (Icc (2 : ℝ) 70111) := by
      apply (hlogc.add continuousOn_const).div
        ((continuousOn_id.pow 2).mul (hlogc.pow 2))
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
      exact mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0)
    have hs := integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hg.integrableOn_Icc
    have ht : IntegrableOn (fun t : ℝ => t * g t) (Icc 2 70111) :=
      (continuousOn_id.mul hg).integrableOn_Icc
    apply (hs.sub ht).congr_fun _ measurableSet_Icc
    intro t ht
    have hc : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = θ t := by
      simp [θ, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter, c]
    change g t * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - t * g t = R t
    rw [hc]
    dsimp [g, R]
    ring
  have htail : IntegrableOn R (Ioi 70111) := by
    apply (majorant_integrable 70111 (by norm_num)).mono' hRmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htt : 70111 < t := ht
    have htpos : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have hbound := hθ t ht.le
    dsimp [R]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < Real.log t + 1),
      abs_of_pos (by positivity : 0 < t ^ 2 * Real.log t ^ 2)]
    calc
      |θ t - t| * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) ≤
          (100 * t / Real.log t ^ 4) * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (by positivity)) (by positivity)
      _ = 100 * (Real.log t + 1) / (t * Real.log t ^ 6) := by
        field_simp [htpos.ne', hl.ne'] <;> ring
  have hu := (hlocal.mono_set Ioc_subset_Icc_self).union htail
  have hsets : Ioc (2 : ℝ) 70111 ∪ Ioi 70111 = Ioi 2 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · linarith
    · intro ht
      by_cases h : t ≤ 70111
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [hsets] at hu
  exact hu
