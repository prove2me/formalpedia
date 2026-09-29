-- Prove2me | solution 1 for WorkbookCorrected.plus_26448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:43:58.00614+00:00
-- url     : https://prove2.me/submissions/cdedc0b7-6f22-4a4f-b111-6e69bb8b275b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (c : ℝ) (hc : c ∈ Set.Icc 0 1) (f : ℕ → ℝ)
    (h0 : f 0 = 0) (h : ∀ n : ℕ, f (n+1)=f n+(c-(f n)^2)/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n-Real.sqrt c| < ε := by
  by_cases hz : c=0
  · have hf : ∀ n : ℕ, f n=0 := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih => rw [h n, ih, hz]; norm_num
    intro ε hε
    refine ⟨0, ?_⟩
    intro n hn
    simpa [hf n,hz] using hε
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hz)
  let s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.mpr hcpos
  have hs2 : s^2=c := Real.sq_sqrt hc.1
  have hs1 : s ≤ 1 := by nlinarith [hc.2]
  let q := 1-s/2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hb : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ s ∧ s-f n ≤ q^n := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num; exact ⟨le_of_lt hs,hs1⟩
    | succ n ih =>
      have hprod := mul_nonneg (sub_nonneg.mpr ih.2.1)
        (show 0 ≤ 2-s-f n by linarith [ih.2.1])
      have hprod2 := mul_nonneg ih.1 (sub_nonneg.mpr ih.2.1)
      have hsquare : (f n)^2 ≤ c := by nlinarith only [ih.1,ih.2.1,hs,hs2]
      have hstep : s-(f n+(c-(f n)^2)/2) ≤ q*(s-f n) := by
        dsimp [q]
        nlinarith only [hprod2,hs2]
      rw [h n]
      refine ⟨by linarith [ih.1], by nlinarith only [hprod,hs2], ?_⟩
      calc
        s-(f n+(c-(f n)^2)/2)  ≤  q*(s-f n) := hstep
        _  ≤  q*q^n := mul_le_mul_of_nonneg_left ih.2.2 hq0
        _ = q^(n+1) := by rw [pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  intro ε hε
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp hp) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hq0 n)] at hh
  have he : |f n-s|=s-f n := by rw [abs_of_nonpos (sub_nonpos.mpr (hb n).2.1)]; ring
  change |f n-s| < ε
  rw [he]
  exact lt_of_le_of_lt (hb n).2.2 hh
example : (∀ (c : ℝ) (hc : c ∈ Set.Icc 0 1) (f : ℕ → ℝ)
    (h0 : f 0 = 0) (h : ∀ n : ℕ, f (n+1)=f n+(c-(f n)^2)/2),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n-Real.sqrt c| < ε) := @solution
#print axioms solution
