-- Prove2me | solution 1 for Rudin.ch07_weierstrass_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:45:03.223543+00:00
-- url     : https://prove2.me/submissions/d5d69a2a-f30d-4eb4-a321-81d64282f4f2

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Set.Icc a b) := by
  classical
  have hre : ContinuousOn (fun x => (f x).re) (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn hf
  have him : ContinuousOn (fun x => (f x).im) (Set.Icc a b) :=
    Complex.continuous_im.comp_continuousOn hf
  choose p hp using fun n : ℕ => exists_polynomial_near_of_continuousOn a b
    (fun x => (f x).re) hre (1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq using fun n : ℕ => exists_polynomial_near_of_continuousOn a b
    (fun x => (f x).im) him (1 / ((n : ℝ) + 1)) (by positivity)
  let P : ℕ → Polynomial ℂ := fun n => (p n).map (algebraMap ℝ ℂ) +
    Polynomial.C Complex.I * (q n).map (algebraMap ℝ ℂ)
  refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have he : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  have hp' := hp n x hx
  have hq' := hq n x hx
  have hev : (P n).eval (x : ℂ) = (((p n).eval x : ℝ) : ℂ) + Complex.I * (((q n).eval x : ℝ) : ℂ) := by
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have hmap (r : Polynomial ℝ) :
        (r.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((r.eval x : ℝ) : ℂ) :=
      Polynomial.eval_map_apply (p := r) (algebraMap ℝ ℂ) x
    rw [hmap, hmap]
  rw [dist_comm, dist_eq_norm, hev]
  have hbound := Complex.norm_le_abs_re_add_abs_im
    ((((p n).eval x : ℝ) : ℂ) + Complex.I * (((q n).eval x : ℝ) : ℂ) - f x)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, zero_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul, zero_add] at hbound
  apply hbound.trans_lt
  calc
    _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hp' hq'
    _ = 2 * (1 / ((n : ℝ) + 1)) := by ring
    _ < ε := hn
#print axioms solution
