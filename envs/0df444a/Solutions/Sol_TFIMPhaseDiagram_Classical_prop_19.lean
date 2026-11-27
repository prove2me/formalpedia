-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_19
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:37:07.581857+00:00
-- url     : https://prove2.me/submissions/346d866a-f746-4c60-928d-77e41620f860

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.P19Aux
open TFIMPhaseDiagram.Classical

lemma p19_logs (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) :
    pairJ r = (1/4) * (Real.log (r (false,false)) + Real.log (r (true,true))
      - Real.log (r (false,true)) - Real.log (r (true,false))) ∧
    pairV1 r = (1/4) * (Real.log (r (false,false)) + Real.log (r (false,true))
      - Real.log (r (true,false)) - Real.log (r (true,true))) ∧
    pairV2 r = (1/4) * (Real.log (r (false,false)) + Real.log (r (true,false))
      - Real.log (r (false,true)) - Real.log (r (true,true))) ∧
    pairC r = Real.exp ((1/4) * (Real.log (r (false,false)) + Real.log (r (false,true))
      + Real.log (r (true,false)) + Real.log (r (true,true)))) := by
  have h1 := hr (false,false); have h2 := hr (false,true)
  have h3 := hr (true,false); have h4 := hr (true,true)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold pairJ
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h4.ne',
      Real.log_mul h2.ne' h3.ne']; ring
  · unfold pairV1
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne',
      Real.log_mul h3.ne' h4.ne']; ring
  · unfold pairV2
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h3.ne',
      Real.log_mul h2.ne' h4.ne']; ring
  · unfold pairC
    have hp : ∏ s, r s = r (false,false) * r (false,true) * (r (true,false) * r (true,true)) := by
      simp only [Fintype.prod_prod_type, Fintype.prod_bool]; ring
    rw [hp, show ∀ a b : ℝ, Real.rpow a b = a ^ b from fun _ _ => rfl, Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
    congr 1; ring

lemma sum4 (x : Bool × Bool → ℝ) : ∑ s, x s =
    x (false,false) + x (false,true) + x (true,false) + x (true,true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]; ring

lemma cov4 (x : Bool × Bool → ℝ) (hS : ∑ s, x s ≠ 0) :
    covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      4 * (x (false,false) * x (true,true) - x (false,true) * x (true,false)) / (∑ s, x s)^2 := by
  have e1 : covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      (x (false,false) - x (false,true) - x (true,false) + x (true,true)) / (∑ s, x s) -
      ((x (false,false) + x (false,true) - x (true,false) - x (true,true)) / (∑ s, x s)) *
      ((x (false,false) - x (false,true) + x (true,false) - x (true,true)) / (∑ s, x s)) := by
    simp only [covariance, normalize, Fintype.sum_prod_type, Fintype.sum_bool, spin]
    simp
    ring
  rw [e1, sum4]; rw [sum4] at hS
  field_simp
  ring

lemma tanh_u (J : ℝ) : Real.tanh J = (Real.exp J ^ 2 - 1) / (Real.exp J ^ 2 + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have := Real.exp_pos J
  field_simp

lemma p19_cov (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) (w : ℝ × ℝ) :
    pairCov r w = 4 * (r (false,false) * r (true,true) - r (false,true) * r (true,false)) /
      (r (false,false) * Real.exp (w.1 + w.2) + r (false,true) * Real.exp (w.1 - w.2) +
        r (true,false) * Real.exp (-w.1 + w.2) + r (true,true) * Real.exp (-w.1 - w.2))^2 := by
  unfold pairCov pairProb
  set x : Bool × Bool → ℝ := fun s => r s * Real.exp (w.1 * spin s.1 + w.2 * spin s.2) with hx
  have hpos : ∀ s, 0 < x s := fun s => mul_pos (hr s) (Real.exp_pos _)
  have hS : ∑ s, x s ≠ 0 := (Finset.sum_pos (fun s _ => hpos s) Finset.univ_nonempty).ne'
  rw [cov4 x hS, sum4]
  have e : ∀ a b : ℝ, Real.exp (a + b) * Real.exp (-a - b) = 1 := by
    intro a b; rw [← Real.exp_add]; simp
  have e2 : ∀ a b : ℝ, Real.exp (a - b) * Real.exp (-a + b) = 1 := by
    intro a b; rw [← Real.exp_add]; simp
  simp only [hx, spin]
  simp only [Bool.false_eq_true, if_false, if_true, mul_one, mul_neg]
  congr 1
  · have h1 := e w.1 w.2; have h2 := e2 w.1 w.2
    rw [show -w.1 + -w.2 = -w.1 - w.2 by ring, show w.1 + -w.2 = w.1 - w.2 by ring]
    linear_combination (4 * r (false,false) * r (true,true)) * h1 -
      (4 * r (false,true) * r (true,false)) * h2

theorem prop_19_aux (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) :
  (∀ s, r s = pairC r * Real.exp (pairJ r * spin s.1 * spin s.2 +
    pairV1 r * spin s.1 + pairV2 r * spin s.2)) ∧
  (∀ (C J v1 v2 : ℝ), 0 < C →
    (∀ s : Bool × Bool, r s = C * Real.exp (J * spin s.1 * spin s.2 + v1*spin s.1 + v2*spin s.2)) →
    C = pairC r ∧ J = pairJ r ∧ v1 = pairV1 r ∧ v2 = pairV2 r) ∧
  |Real.tanh (pairJ r)| = sSup (Set.range (fun w : ℝ × ℝ => |pairCov r w|)) := by
  obtain ⟨hJ, hV1, hV2, hC⟩ := p19_logs r hr
  have h1 := hr (false,false); have h2 := hr (false,true)
  have h3 := hr (true,false); have h4 := hr (true,true)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_ | _, _ | _⟩ <;>
    · rw [hC, hJ, hV1, hV2, ← Real.exp_add]
      conv_lhs => rw [← Real.exp_log (hr _)]
      congr 1; simp [spin]; ring
  · intro C J v1 v2 hCpos h
    have hl : ∀ s : Bool × Bool, Real.log (r s) =
        Real.log C + (J * spin s.1 * spin s.2 + v1*spin s.1 + v2*spin s.2) := by
      intro s; rw [h s, Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have a1 := hl (false,false); have a2 := hl (false,true)
    have a3 := hl (true,false); have a4 := hl (true,true)
    simp only [spin, Bool.false_eq_true, if_false, if_true] at a1 a2 a3 a4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hC, a1, a2, a3, a4]; conv_lhs => rw [← Real.exp_log hCpos]
      congr 1; ring
    · rw [hJ, a1, a2, a3, a4]; ring
    · rw [hV1, a1, a2, a3, a4]; ring
    · rw [hV2, a1, a2, a3, a4]; ring
  · set u := Real.exp (pairJ r) with hu
    have hupos : 0 < u := Real.exp_pos _
    set P := r (false,false) * r (true,true)
    set Q := r (false,true) * r (true,false)
    have hP : 0 < P := mul_pos h1 h4
    have hQ : 0 < Q := mul_pos h2 h3
    have hu4 : u ^ 4 * Q = P := by
      have : u ^ 4 = Real.exp (4 * pairJ r) := by
        rw [hu, ← Real.exp_nat_mul]; norm_num
      rw [this]; unfold pairJ
      rw [show 4 * (1 / 4 * Real.log (r (false, false) * r (true, true) /
        (r (false, true) * r (true, false)))) = Real.log (P / Q) by ring,
        Real.exp_log (div_pos hP hQ)]
      field_simp
    have htanh := tanh_u (pairJ r)
    rw [← hu] at htanh
    -- the bound
    have bound : ∀ w : ℝ × ℝ, |pairCov r w| ≤ |Real.tanh (pairJ r)| := by
      intro w
      rw [p19_cov r hr w, htanh]
      set A := r (false,false) * Real.exp (w.1 + w.2)
      set B := r (false,true) * Real.exp (w.1 - w.2)
      set C := r (true,false) * Real.exp (-w.1 + w.2)
      set D := r (true,true) * Real.exp (-w.1 - w.2)
      have hA : 0 < A := mul_pos h1 (Real.exp_pos _)
      have hB : 0 < B := mul_pos h2 (Real.exp_pos _)
      have hC' : 0 < C := mul_pos h3 (Real.exp_pos _)
      have hD : 0 < D := mul_pos h4 (Real.exp_pos _)
      have hAD : A * D = P := by
        simp only [A, D, P]
        rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf; simp
      have hBC : B * C = Q := by
        simp only [B, C, Q]
        rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf; simp
      have k1 : (A + D)^2 ≥ 4 * u^4 * Q := by nlinarith [sq_nonneg (A - D)]
      have k2 : (B + C)^2 ≥ 4 * Q := by nlinarith [sq_nonneg (B - C)]
      have k3 : (A + D) * (B + C) ≥ 4 * u^2 * Q := by
        have : (4 * u^2 * Q)^2 ≤ ((A + D) * (B + C))^2 := by
          rw [mul_pow]; nlinarith [mul_le_mul k1 k2 (by positivity) (by positivity)]
        exact (sq_le_sq₀ (by positivity) (by positivity)).1 this
      have kS : 4 * Q * (u^2 + 1)^2 ≤ (A + B + C + D)^2 := by nlinarith
      have hnum : |4 * (P - Q)| = 4 * Q * |u^2 - 1| * (u^2 + 1) := by
        rw [← hu4, show 4 * (u ^ 4 * Q - Q) = (4 * Q * (u^2+1)) * (u^2 - 1) by ring, abs_mul,
          abs_of_pos (by positivity)]; ring
      rw [abs_div, abs_div, hnum, abs_of_pos (by positivity : (0:ℝ) < (A+B+C+D)^2),
        abs_of_pos (by positivity : (0:ℝ) < u^2 + 1)]
      calc 4 * Q * |u ^ 2 - 1| * (u ^ 2 + 1) / (A + B + C + D) ^ 2
          ≤ 4 * Q * |u ^ 2 - 1| * (u ^ 2 + 1) / (4 * Q * (u^2 + 1)^2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) kS
        _ = |u ^ 2 - 1| / (u ^ 2 + 1) := by field_simp
    -- attainment
    set la := Real.log (r (false,false)); set lb := Real.log (r (false,true))
    set lc := Real.log (r (true,false)); set ld := Real.log (r (true,true))
    set wst : ℝ × ℝ := ((1/4) * (ld - la + lc - lb), (1/4) * (ld - la - lc + lb))
    have attain : |pairCov r wst| = |Real.tanh (pairJ r)| := by
      rw [p19_cov r hr wst, htanh]
      set p := Real.exp ((la + ld)/2); set q := Real.exp ((lb + lc)/2)
      have ea : r (false,false) * Real.exp (wst.1 + wst.2) = p := by
        conv_lhs => rw [← Real.exp_log h1]
        rw [← Real.exp_add]; congr 1; simp only [wst, la]; ring
      have eb : r (false,true) * Real.exp (wst.1 - wst.2) = q := by
        conv_lhs => rw [← Real.exp_log h2]
        rw [← Real.exp_add]; congr 1; simp only [wst, lb, lc]; ring
      have ec : r (true,false) * Real.exp (-wst.1 + wst.2) = q := by
        conv_lhs => rw [← Real.exp_log h3]
        rw [← Real.exp_add]; congr 1; simp only [wst, lb, lc]; ring
      have ed : r (true,true) * Real.exp (-wst.1 - wst.2) = p := by
        conv_lhs => rw [← Real.exp_log h4]
        rw [← Real.exp_add]; congr 1; simp only [wst, la, ld]; ring
      have hpP : p ^ 2 = P := by
        rw [← Real.exp_nat_mul, show ((2:ℕ):ℝ) * ((la + ld)/2) = la + ld by push_cast; ring,
          Real.exp_add, Real.exp_log h1, Real.exp_log h4]
      have hqQ : q ^ 2 = Q := by
        rw [← Real.exp_nat_mul, show ((2:ℕ):ℝ) * ((lb + lc)/2) = lb + lc by push_cast; ring,
          Real.exp_add, Real.exp_log h2, Real.exp_log h3]
      have huq : u ^ 2 * q = p := by
        rw [hu, ← Real.exp_nat_mul, ← Real.exp_add, hJ]; congr 1; push_cast; ring
      have hp : 0 < p := Real.exp_pos _
      have hq : 0 < q := Real.exp_pos _
      rw [ea, eb, ec, ed]
      change |4 * (P - Q) / _| = _
      rw [← hpP, ← hqQ, ← huq]
      congr 1
      field_simp
      ring
    symm
    apply IsGreatest.csSup_eq
    refine ⟨⟨wst, attain⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact bound w

end TFIMPhaseDiagram.Classical.P19Aux

open TFIMPhaseDiagram.Classical in
theorem solution (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) :
  (∀ s, r s = pairC r * Real.exp (pairJ r * spin s.1 * spin s.2 +
    pairV1 r * spin s.1 + pairV2 r * spin s.2)) ∧
  (∀ (C J v1 v2 : ℝ), 0 < C →
    (∀ s : Bool × Bool, r s = C * Real.exp (J * spin s.1 * spin s.2 + v1*spin s.1 + v2*spin s.2)) →
    C = pairC r ∧ J = pairJ r ∧ v1 = pairV1 r ∧ v2 = pairV2 r) ∧
  |Real.tanh (pairJ r)| = sSup (Set.range (fun w : ℝ × ℝ => |pairCov r w|)) :=
  TFIMPhaseDiagram.Classical.P19Aux.prop_19_aux r hr
