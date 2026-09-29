-- Prove2me | solution 1 for TaoFivePrimes.typeII_dyadic_integration
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:40:12.497595+00:00
-- url     : https://prove2.me/submissions/a6309738-15aa-43c5-a20e-f1ed13eef106

import Mathlib

open MeasureTheory intervalIntegral

section PartTII
open MeasureTheory intervalIntegral

namespace TaoTII

theorem pos_of_mem_uIcc {b c W : ℝ} (hb : 0 < b) (hbc : b ≤ c) (hW : W ∈ Set.uIcc b c) :
    0 < W := by
  rw [Set.uIcc_of_le hbc] at hW
  exact lt_of_lt_of_le hb hW.1

theorem int_inv_sqrt (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    (∫ W in b..c, 1 / Real.sqrt W) = 2 * Real.sqrt c - 2 * Real.sqrt b := by
  have hderiv : ∀ W ∈ Set.uIcc b c,
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (1 / Real.sqrt W) W := by
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hb hbc hW
    have hs : Real.sqrt W ≠ 0 := by positivity
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hW0)).const_mul (2:ℝ)
    have heq : (2:ℝ) * (1 / (2 * Real.sqrt W)) = 1 / Real.sqrt W := by field_simp
    rwa [heq] at h
  have hint : IntervalIntegrable (fun W : ℝ => 1 / Real.sqrt W) volume b c := by
    apply ContinuousOn.intervalIntegrable
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hb hbc hW
    have hcont : ContinuousAt (fun W : ℝ => 1 / Real.sqrt W) W := by
      refine ContinuousAt.div continuousAt_const (Real.continuous_sqrt.continuousAt) ?_
      positivity
    exact hcont.continuousWithinAt
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using h

theorem int_inv_sqrt_cube (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    (∫ W in b..c, 1 / (W * Real.sqrt W)) = 2 / Real.sqrt b - 2 / Real.sqrt c := by
  have hderiv : ∀ W ∈ Set.uIcc b c,
      HasDerivAt (fun t : ℝ => (-2 : ℝ) / Real.sqrt t) (1 / (W * Real.sqrt W)) W := by
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hb hbc hW
    have hs : Real.sqrt W ≠ 0 := by positivity
    have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt W)) W := Real.hasDerivAt_sqrt (ne_of_gt hW0)
    have h := (hasDerivAt_const W (-2:ℝ)).div h1 hs
    have heq : ((0:ℝ) * Real.sqrt W - (-2) * (1 / (2 * Real.sqrt W))) / Real.sqrt W ^ 2
        = 1 / (W * Real.sqrt W) := by
      rw [Real.sq_sqrt hW0.le]
      field_simp
      ring
    rwa [heq] at h
  have hint : IntervalIntegrable (fun W : ℝ => 1 / (W * Real.sqrt W)) volume b c := by
    apply ContinuousOn.intervalIntegrable
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hb hbc hW
    have hcont : ContinuousAt (fun W : ℝ => 1 / (W * Real.sqrt W)) W := by
      refine ContinuousAt.div continuousAt_const
        (continuousAt_id.mul Real.continuous_sqrt.continuousAt) ?_
      have hsw : 0 < Real.sqrt W := by positivity
      have : (0:ℝ) < id W * Real.sqrt W := by simpa using mul_pos hW0 hsw
      exact ne_of_gt this
    exact hcont.continuousWithinAt
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le hb hbc
  have hb' : Real.sqrt b ≠ 0 := by positivity
  have hc' : Real.sqrt c ≠ 0 := by positivity
  field_simp
  ring

end TaoTII

namespace TaoTII
open MeasureTheory intervalIntegral

set_option maxHeartbeats 2000000 in
theorem dyadic_integration (x q U V : ℝ) (G : ℝ → ℝ)
    (hx : 0 < x) (hq : 4 ≤ q) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUV : U * V ≤ x / 4)
    (hG0 : ∀ W, 0 ≤ G W)
    (hGsupp : ∀ W, W ∉ Set.Icc V (x / U) → G W = 0)
    (hGint : IntegrableOn (fun W => G W / W) (Set.Ioi 0))
    (hGb : ∀ W ∈ Set.Icc V (x / U),
        G W ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * q)) * Real.log W) :
    4 * ∫ W in Set.Ioi (0:ℝ), G W / W ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by
  have hU0 : (0:ℝ) < U := by linarith
  have hV0 : (0:ℝ) < V := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  set B : ℝ := x / U with hB
  have hVB4 : V ≤ x / (4 * U) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hVB : V ≤ B := by
    rw [hB]
    have : x / (4 * U) ≤ x / U := by
      apply div_le_div_of_nonneg_left hx.le hU0 (by linarith)
    linarith
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le hV0 hVB
  have hB160 : (160:ℝ) ≤ B := by
    rw [hB, le_div_iff₀ hU0]
    nlinarith
  have hLB : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
  have hLV : (0:ℝ) ≤ Real.log V := Real.log_nonneg (by linarith)
  have hLVB : Real.log V ≤ Real.log B := Real.log_le_log hV0 hVB
  ---- restrict the integral to [V, B]
  have hsub : Set.Icc V B ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_of_lt_of_le hV0 ht.1
  have hzero : ∀ t ∈ Set.Ioi (0:ℝ) \ Set.Icc V B, G t / t = 0 := by
    intro t ht
    rw [hGsupp t ht.2, zero_div]
  have hres : (∫ W in Set.Ioi (0:ℝ), G W / W) = ∫ W in Set.Icc V B, G W / W :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hzero
  have hIcc : (∫ W in Set.Icc V B, G W / W) = ∫ W in V..B, G W / W := by
    rw [intervalIntegral.integral_of_le hVB, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hfint : IntervalIntegrable (fun W => G W / W) volume V B := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hVB]
    exact hGint.mono_set (fun t ht => lt_trans hV0 ht.1)
  ---- the majorant
  set K : ℝ := (1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q) + Real.sqrt 2 * Real.sqrt (x * q)
    with hK
  set g : ℝ → ℝ := fun W => (1.1/8) * K * (Real.log W / W)
      + (1.1/8) * (1/2) * Real.sqrt x * Real.log B * (1 / Real.sqrt W)
      + (1.1/8) * x * Real.log B * (1 / (W * Real.sqrt W)) with hg
  have hK0 : (0:ℝ) ≤ K := by
    rw [hK]; positivity
  have hcont : ∀ W ∈ Set.uIcc V B, ContinuousAt g W := by
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hV0 hVB hW
    have hsW : (0:ℝ) < Real.sqrt W := by positivity
    rw [hg]
    refine ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_
    · exact continuousAt_const.mul
        (ContinuousAt.div (Real.continuousAt_log hW0.ne') continuousAt_id hW0.ne')
    · exact continuousAt_const.mul
        (ContinuousAt.div continuousAt_const Real.continuous_sqrt.continuousAt hsW.ne')
    · refine continuousAt_const.mul (ContinuousAt.div continuousAt_const
        (continuousAt_id.mul Real.continuous_sqrt.continuousAt) ?_)
      have : (0:ℝ) < id W * Real.sqrt W := by simpa using mul_pos hW0 hsW
      exact ne_of_gt this
  have hgint : IntervalIntegrable g volume V B :=
    ContinuousOn.intervalIntegrable (fun W hW => (hcont W hW).continuousWithinAt)
  ---- pointwise domination
  have hmono : ∀ W ∈ Set.Icc V B, G W / W ≤ g W := by
    intro W hW
    have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
    have hsW : (0:ℝ) < Real.sqrt W := by positivity
    have hlW : (0:ℝ) ≤ Real.log W := Real.log_nonneg (by linarith [hW.1])
    have hlWB : Real.log W ≤ Real.log B := Real.log_le_log hW0 hW.2
    have hb := hGb W hW
    have hsplit : Real.sqrt (x * W) / W = Real.sqrt x / Real.sqrt W := by
      rw [Real.sqrt_mul hx.le]
      rw [div_eq_div_iff hW0.ne' hsW.ne']
      nlinarith [Real.mul_self_sqrt hW0.le, Real.sqrt_nonneg x]
    have h1 : G W / W ≤ ((1.1/8) * (K + (1/2) * Real.sqrt (x * W) + x / Real.sqrt W)
        * Real.log W) / W := by
      rw [div_le_div_iff_of_pos_right hW0]
      refine le_trans hb (le_of_eq ?_)
      rw [hK]; ring
    refine le_trans h1 ?_
    have hexp : ((1.1/8) * (K + (1/2) * Real.sqrt (x * W) + x / Real.sqrt W) * Real.log W) / W
        = (1.1/8) * K * (Real.log W / W)
          + (1.1/8) * (1/2) * Real.sqrt x * Real.log W * (1 / Real.sqrt W)
          + (1.1/8) * x * Real.log W * (1 / (W * Real.sqrt W)) := by
      have hxW : Real.sqrt (x * W) = Real.sqrt x * Real.sqrt W := Real.sqrt_mul hx.le W
      obtain ⟨s, hs0, hsq, hWs⟩ : ∃ s : ℝ, 0 < s ∧ Real.sqrt W = s ∧ W = s * s :=
        ⟨Real.sqrt W, hsW, rfl, (Real.mul_self_sqrt hW0.le).symm⟩
      rw [hxW, hsq, hWs]
      field_simp
    rw [hexp, hg]
    have t2 : (1.1/8) * (1/2) * Real.sqrt x * Real.log W * (1 / Real.sqrt W)
        ≤ (1.1/8) * (1/2) * Real.sqrt x * Real.log B * (1 / Real.sqrt W) := by
      have : (0:ℝ) ≤ (1.1/8) * (1/2) * Real.sqrt x * (1 / Real.sqrt W) := by positivity
      nlinarith
    have t3 : (1.1/8) * x * Real.log W * (1 / (W * Real.sqrt W))
        ≤ (1.1/8) * x * Real.log B * (1 / (W * Real.sqrt W)) := by
      have : (0:ℝ) ≤ (1.1/8) * x * (1 / (W * Real.sqrt W)) := by positivity
      nlinarith
    linarith
  ---- integrability of the three pieces
  have iint1 : IntervalIntegrable (fun W : ℝ => Real.log W / W) volume V B := by
    apply ContinuousOn.intervalIntegrable
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hV0 hVB hW
    exact (ContinuousAt.div (Real.continuousAt_log hW0.ne') continuousAt_id
      hW0.ne').continuousWithinAt
  have iint2 : IntervalIntegrable (fun W : ℝ => 1 / Real.sqrt W) volume V B := by
    apply ContinuousOn.intervalIntegrable
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hV0 hVB hW
    have hsW : (0:ℝ) < Real.sqrt W := by positivity
    exact (ContinuousAt.div continuousAt_const Real.continuous_sqrt.continuousAt
      hsW.ne').continuousWithinAt
  have iint3 : IntervalIntegrable (fun W : ℝ => 1 / (W * Real.sqrt W)) volume V B := by
    apply ContinuousOn.intervalIntegrable
    intro W hW
    have hW0 : 0 < W := pos_of_mem_uIcc hV0 hVB hW
    have hsW : (0:ℝ) < Real.sqrt W := by positivity
    refine (ContinuousAt.div continuousAt_const
      (continuousAt_id.mul Real.continuous_sqrt.continuousAt) ?_).continuousWithinAt
    have : (0:ℝ) < id W * Real.sqrt W := by simpa using mul_pos hW0 hsW
    exact ne_of_gt this
  ---- the three integrals
  have hi1 : (∫ W in V..B, Real.log W / W)
      = (Real.log B * Real.log B - Real.log V * Real.log V) / 2 := by
    have hderiv : ∀ W ∈ Set.uIcc V B,
        HasDerivAt (fun t : ℝ => Real.log t * Real.log t / 2) (Real.log W / W) W := by
      intro W hW
      have hW0 : 0 < W := pos_of_mem_uIcc hV0 hVB hW
      have h1 : HasDerivAt Real.log W⁻¹ W := Real.hasDerivAt_log hW0.ne'
      have h2 := (h1.mul h1).div_const 2
      have heq : (W⁻¹ * Real.log W + Real.log W * W⁻¹) / 2 = Real.log W / W := by
        field_simp; ring
      rwa [heq] at h2
    have h := integral_eq_sub_of_hasDerivAt hderiv iint1
    rw [h]; ring
  have hi2 := int_inv_sqrt V B hV0 hVB
  have hi3 := int_inv_sqrt_cube V B hV0 hVB
  have hle : (∫ W in V..B, G W / W) ≤ ∫ W in V..B, g W :=
    intervalIntegral.integral_mono_on hVB hfint hgint hmono
  have hgval : (∫ W in V..B, g W)
      = (1.1/8) * K * ((Real.log B * Real.log B - Real.log V * Real.log V) / 2)
        + (1.1/8) * (1/2) * Real.sqrt x * Real.log B * (2 * Real.sqrt B - 2 * Real.sqrt V)
        + (1.1/8) * x * Real.log B * (2 / Real.sqrt V - 2 / Real.sqrt B) := by
    rw [hg]
    rw [intervalIntegral.integral_add ((iint1.const_mul _).add (iint2.const_mul _))
        (iint3.const_mul _),
      intervalIntegral.integral_add (iint1.const_mul _) (iint2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hi1, hi2, hi3]
  ---- numerical facts
  have hs2l : (1.4142:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.4142:ℝ) = Real.sqrt (1.4142^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2u : Real.sqrt 2 ≤ 1.41422 := by
    rw [show (1.41422:ℝ) = Real.sqrt (1.41422^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq : Real.sqrt (x * q) = x / Real.sqrt (x / q) := by
    have hs0 : (0:ℝ) < Real.sqrt (x / q) := Real.sqrt_pos.mpr (by positivity)
    have h1 : x * q = (x / Real.sqrt (x / q)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ x / q)]
      field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hsqxB : Real.sqrt x * Real.sqrt B = x / Real.sqrt U := by
    rw [← Real.sqrt_mul hx.le]
    have h1 : x * B = (x / Real.sqrt U) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hU0.le, hB]
      field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hKb : 0.275 * K ≤ 0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q) := by
    have ha : (0:ℝ) ≤ x / Real.sqrt q := by positivity
    have hb2 : (0:ℝ) ≤ x / Real.sqrt (x / q) := by positivity
    have hs20 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h1 : 0.275 * (1 / (2 * Real.sqrt 2)) ≤ 0.1 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt 2)]
      nlinarith
    have h2 : 0.275 * Real.sqrt 2 ≤ 0.39 := by nlinarith
    have p1 : (0.275 * (1 / (2 * Real.sqrt 2))) * (x / Real.sqrt q) ≤ 0.1 * (x / Real.sqrt q) :=
      mul_le_mul_of_nonneg_right h1 ha
    have p2 : (0.275 * Real.sqrt 2) * (x / Real.sqrt (x / q))
        ≤ 0.39 * (x / Real.sqrt (x / q)) :=
      mul_le_mul_of_nonneg_right h2 hb2
    rw [hK, hsq]
    have expand : 0.275 * (1 / (2 * Real.sqrt 2) * (x / Real.sqrt q)
        + Real.sqrt 2 * (x / Real.sqrt (x / q)))
        = 0.275 * (1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
          + 0.275 * Real.sqrt 2 * (x / Real.sqrt (x / q)) := by ring
    have g1 : 0.1 * x / Real.sqrt q = 0.1 * (x / Real.sqrt q) := by ring
    have g2 : 0.39 * x / Real.sqrt (x / q) = 0.39 * (x / Real.sqrt (x / q)) := by ring
    rw [expand, g1, g2]
    exact add_le_add p1 p2
  have hPQ : Real.log (x / (U * V)) * Real.log (V * x / U)
      = Real.log B * Real.log B - Real.log V * Real.log V := by
    have e1 : x / (U * V) = B / V := by rw [hB]; field_simp
    have e2 : V * x / U = V * B := by rw [hB]; field_simp
    rw [e1, e2, Real.log_div hB0.ne' hV0.ne', Real.log_mul hV0.ne' hB0.ne']
    ring
  have hdiff : (0:ℝ) ≤ Real.log B * Real.log B - Real.log V * Real.log V := by
    have := mul_le_mul hLVB hLVB hLV (le_trans hLV hLVB)
    linarith
  have hA : 0.275 * K * (Real.log B * Real.log B - Real.log V * Real.log V)
      ≤ (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
        * (Real.log B * Real.log B - Real.log V * Real.log V) :=
    mul_le_mul_of_nonneg_right hKb hdiff
  have hB' : 0.55 * Real.sqrt x * Real.log B * (Real.sqrt B - Real.sqrt V)
      ≤ 0.55 * (x / Real.sqrt U) * Real.log B := by
    have h1 : 0.55 * Real.sqrt x * Real.log B * (Real.sqrt B - Real.sqrt V)
        = 0.55 * Real.log B * (Real.sqrt x * Real.sqrt B)
          - 0.55 * Real.log B * (Real.sqrt x * Real.sqrt V) := by ring
    have h2 : (0:ℝ) ≤ 0.55 * Real.log B * (Real.sqrt x * Real.sqrt V) :=
      mul_nonneg (mul_nonneg (by norm_num) hLB)
        (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg V))
    rw [h1, hsqxB]
    linarith
  have hC : 1.1 * x * Real.log B * (1 / Real.sqrt V - 1 / Real.sqrt B)
      ≤ 1.1 * (x / Real.sqrt V) * Real.log B := by
    have hsB : (0:ℝ) < Real.sqrt B := by positivity
    have hsV : (0:ℝ) < Real.sqrt V := by positivity
    have h1 : (0:ℝ) ≤ 1.1 * x * Real.log B * (1 / Real.sqrt B) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx.le) hLB) (by positivity)
    have h2 : 1.1 * x * Real.log B * (1 / Real.sqrt V) = 1.1 * (x / Real.sqrt V) * Real.log B := by
      field_simp
    have h3 : 1.1 * x * Real.log B * (1 / Real.sqrt V - 1 / Real.sqrt B)
        = 1.1 * x * Real.log B * (1 / Real.sqrt V)
          - 1.1 * x * Real.log B * (1 / Real.sqrt B) := by ring
    rw [h3, h2]
    linarith
  ---- assemble
  rw [hres, hIcc]
  have htarget : (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
        * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log B
      = (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
        * (Real.log B * Real.log B - Real.log V * Real.log V)
        + 0.55 * (x / Real.sqrt U) * Real.log B + 1.1 * (x / Real.sqrt V) * Real.log B := by
    rw [← hPQ]; ring
  rw [htarget]
  have h4 : 4 * (∫ W in V..B, g W)
      = 0.275 * K * (Real.log B * Real.log B - Real.log V * Real.log V)
        + 0.55 * Real.sqrt x * Real.log B * (Real.sqrt B - Real.sqrt V)
        + 1.1 * x * Real.log B * (1 / Real.sqrt V - 1 / Real.sqrt B) := by
    rw [hgval]; ring
  calc 4 * (∫ W in V..B, G W / W) ≤ 4 * (∫ W in V..B, g W) := by linarith
    _ = 0.275 * K * (Real.log B * Real.log B - Real.log V * Real.log V)
        + 0.55 * Real.sqrt x * Real.log B * (Real.sqrt B - Real.sqrt V)
        + 1.1 * x * Real.log B * (1 / Real.sqrt V - 1 / Real.sqrt B) := h4
    _ ≤ (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
        * (Real.log B * Real.log B - Real.log V * Real.log V)
        + 0.55 * (x / Real.sqrt U) * Real.log B
        + 1.1 * (x / Real.sqrt V) * Real.log B := by
      linarith only [hA, hB', hC]

end TaoTII

end PartTII

theorem solution (x q U V : ℝ) (G : ℝ → ℝ)
    (hx : 0 < x) (hq : 4 ≤ q) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUV : U * V ≤ x / 4)
    (hG0 : ∀ W, 0 ≤ G W)
    (hGsupp : ∀ W, W ∉ Set.Icc V (x / U) → G W = 0)
    (hGint : MeasureTheory.IntegrableOn (fun W => G W / W) (Set.Ioi 0))
    (hGb : ∀ W ∈ Set.Icc V (x / U),
        G W ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * q)) * Real.log W) :
    4 * ∫ W in Set.Ioi (0:ℝ), G W / W ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) :=
  TaoTII.dyadic_integration x q U V G hx hq hU40 hV40 hUV hG0 hGsupp hGint hGb
