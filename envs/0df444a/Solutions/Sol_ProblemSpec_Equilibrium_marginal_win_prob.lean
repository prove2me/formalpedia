-- Prove2me | solution 1 for ProblemSpec.Equilibrium.marginal_win_prob
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:01:27.595722+00:00
-- url     : https://prove2.me/submissions/c2de1d14-6f69-4e77-8c20-974f91b80d7e

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace Aux_PS_mwp

lemma gen (m C a : ℝ) (Q : ℝ → ℝ) (r : ℝ) (hm : 0 < m) (hC : 0 < C) (hQ : HasDerivAt Q a r) :
    HasDerivAt (fun x => m * Real.exp (Q x) / (m * Real.exp (Q x) + C))
      (m * Real.exp (Q r) * a * C / (m * Real.exp (Q r) + C) ^ 2) r := by
  have h1 := hQ.exp.const_mul m
  have h2 := h1.add_const C
  have hne : m * Real.exp (Q r) + C ≠ 0 := by positivity
  have := h1.div h2 hne
  refine this.congr_deriv ?_
  ring

lemma value (m e a N : ℝ) (hm : 0 < m) (he : 0 < e) (hN : 1 < N) :
    m * e * a * ((N - 1) * m * e) / (m * e + (N - 1) * m * e) ^ 2 = a * ((N - 1) / N ^ 2) := by
  have hN0 : N ≠ 0 := by linarith
  have : m * e + (N - 1) * m * e = N * (m * e) := by ring
  rw [this]
  have : m * e ≠ 0 := by positivity
  field_simp

end Aux_PS_mwp

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr N r m : ℝ) (hN : 1 < N)
    (hm : 0 < m) :
    (Sr < r → HasDerivAt (fun x => winProb P Sr N x m r m)
        (P.ν * P.w / P.μ * ((N - 1) / N ^ 2)) r) ∧
    (r < Sr → HasDerivAt (fun x => winProb P Sr N x m r m)
        (P.w / P.μ * ((N - 1) / N ^ 2)) r) := by
  have hC : 0 < (N - 1) * m * Real.exp (quality P Sr r / P.μ) := by
    have : 0 < N - 1 := by linarith
    positivity
  constructor
  · intro h
    have hqr : quality P Sr r = Sr * P.w + (r - Sr) * P.ν * P.w := by
      unfold quality; rw [if_neg (not_le.mpr h)]
    have hQ : HasDerivAt (fun x : ℝ => (Sr * P.w + (x - Sr) * P.ν * P.w) / P.μ)
        (1 * P.ν * P.w / P.μ) r :=
      ((((hasDerivAt_id' (x := r)).sub_const Sr).mul_const P.ν).mul_const P.w).const_add
        (Sr * P.w) |>.div_const P.μ
    have hg := Aux_PS_mwp.gen m _ _ _ r hm hC hQ
    refine (hg.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hqr]
      rw [Aux_PS_mwp.value m _ _ N hm (Real.exp_pos _) hN]
      ring
    · filter_upwards [Ioi_mem_nhds h] with x hx
      unfold winProb
      have : quality P Sr x = Sr * P.w + (x - Sr) * P.ν * P.w := by
        unfold quality; rw [if_neg (not_le.mpr hx)]
      rw [this]
  · intro h
    have hqr : quality P Sr r = r * P.w := by
      unfold quality; rw [if_pos h.le]
    have hQ : HasDerivAt (fun x : ℝ => x * P.w / P.μ) (1 * P.w / P.μ) r :=
      ((hasDerivAt_id' (x := r)).mul_const P.w).div_const P.μ
    have hg := Aux_PS_mwp.gen m _ _ _ r hm hC hQ
    refine (hg.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hqr]
      rw [Aux_PS_mwp.value m _ _ N hm (Real.exp_pos _) hN]
      ring
    · filter_upwards [Iio_mem_nhds h] with x hx
      unfold winProb
      have : quality P Sr x = x * P.w := by
        unfold quality; rw [if_pos hx.le]
      rw [this]
