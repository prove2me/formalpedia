-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_75
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T14:26:49.010011+00:00
-- url     : https://prove2.me/submissions/8a23fd12-fea7-40e6-b350-18d617dfd9a8

import Mathlib

open Complex

theorem solution (a : ℕ) (ha : 1 ≤ a) (c : ℂ) (ρ : ℝ) (hc : ‖c‖ < ρ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (∮ w in C(c, ρ), exp w / w ^ a) = 1 / ((a - 1).factorial : ℂ) ∧
      1 / ((a - 1).factorial : ℂ) = 1 / Gamma (a : ℂ) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg c) hc
  have hball : (0 : ℂ) ∈ Metric.ball c ρ := by
    rw [Metric.mem_ball, dist_zero_left]
    exact hc
  have hzero_sphere : ∀ z ∈ Metric.sphere c ρ, z ≠ 0 := by
    intro z hz hz0
    have h1 : dist z c = ρ := Metric.mem_sphere.1 hz
    rw [hz0, dist_zero_left] at h1
    linarith
  have hbase : (∮ w in C(c, ρ), exp w / w ^ 1) = 2 * (Real.pi : ℂ) * I := by
    have h := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (R := ρ) (c := c) (w := (0 : ℂ)) (f := fun z : ℂ => exp z) (s := (∅ : Set ℂ))
      Set.countable_empty hball continuous_exp.continuousOn
      (fun x _ => differentiableAt_exp)
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using h
  let J : ℕ → ℂ := fun n => ∮ w in C(c, ρ), exp w * w ^ (-(n : ℤ))
  have hcontJ : ∀ n : ℕ, ContinuousOn (fun z : ℂ => exp z * z ^ (-(n : ℤ))) (Metric.sphere c ρ) := by
    intro n
    exact continuous_exp.continuousOn.mul
      ((continuousOn_zpow₀ (-(n : ℤ))).mono (fun z hz => hzero_sphere z hz))
  have hJ1 : J 1 = 2 * (Real.pi : ℂ) * I := by
    rw [← hbase]
    dsimp only [J]
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    simp [div_eq_mul_inv, zpow_neg]
  have hstep : ∀ n : ℕ, 1 ≤ n → J n = (n : ℂ) * J (n + 1) := by
    intro n hn
    have hderiv : ∀ z ∈ Metric.sphere c ρ,
        HasDerivWithinAt (fun w : ℂ => exp w * w ^ (-(n : ℤ)))
          (exp z * z ^ (-(n : ℤ)) -
            (n : ℂ) * (exp z * z ^ (-((n + 1 : ℕ) : ℤ)))) (Metric.sphere c ρ) z := by
      intro z hz
      have hz0 : z ≠ 0 := hzero_sphere z hz
      have h1 : HasDerivAt (fun w : ℂ => exp w) (exp z) z := Complex.hasDerivAt_exp z
      have h2 : HasDerivAt (fun w : ℂ => w ^ (-(n : ℤ)))
          (((-(n : ℤ) : ℤ) : ℂ) * z ^ (-(n : ℤ) - 1)) z :=
        hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz0)
      have h3 := h1.mul h2
      have hval : exp z * z ^ (-(n : ℤ)) +
            exp z * ((((-(n : ℤ)) : ℤ) : ℂ) * z ^ (-(n : ℤ) - 1)) =
          exp z * z ^ (-(n : ℤ)) - (n : ℂ) * (exp z * z ^ (-((n + 1 : ℕ) : ℤ))) := by
        have hexp : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hexp]
        push_cast
        ring
      rw [hval] at h3
      exact h3.hasDerivWithinAt
    have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hρ.le hderiv
    have hint1 : CircleIntegrable (fun z : ℂ => exp z * z ^ (-(n : ℤ))) c ρ :=
      (hcontJ n).circleIntegrable hρ.le
    have hint2 : CircleIntegrable
        (fun z : ℂ => (n : ℂ) * (exp z * z ^ (-((n + 1 : ℕ) : ℤ)))) c ρ :=
      (continuousOn_const.mul (hcontJ (n + 1))).circleIntegrable hρ.le
    rw [circleIntegral.integral_sub hint1 hint2, circleIntegral.integral_const_mul] at hzero
    dsimp only [J] at hzero ⊢
    rwa [sub_eq_zero] at hzero
  have hJmain : ∀ n : ℕ, 1 ≤ n →
      (2 * (Real.pi : ℂ) * I)⁻¹ * J n = 1 / ((n - 1).factorial : ℂ) := by
    intro n
    induction n with
    | zero =>
      intro hn
      omega
    | succ m ih =>
      intro hm
      cases m with
      | zero =>
        have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ * J 1 = 1 / ((1 - 1).factorial : ℂ) := by
          rw [hJ1, inv_mul_cancel₀ two_pi_I_ne_zero]
          simp
        simpa using h1
      | succ k =>
        have hIH : (2 * (Real.pi : ℂ) * I)⁻¹ * J (k + 1) =
            1 / (((k + 1) - 1).factorial : ℂ) := ih (by omega)
        have hrec : J (k + 1) = ((k + 1 : ℕ) : ℂ) * J (k + 1 + 1) :=
          hstep (k + 1) (by omega)
        have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have hJnext : J (k + 1 + 1) = J (k + 1) / ((k + 1 : ℕ) : ℂ) := by
          rw [hrec]
          field_simp
        calc
          (2 * (Real.pi : ℂ) * I)⁻¹ * J (k + 1 + 1)
              = (2 * (Real.pi : ℂ) * I)⁻¹ *
                  (J (k + 1) / ((k + 1 : ℕ) : ℂ)) := by rw [hJnext]
          _ = ((2 * (Real.pi : ℂ) * I)⁻¹ * J (k + 1)) / ((k + 1 : ℕ) : ℂ) := by ring
          _ = (1 / (((k + 1) - 1).factorial : ℂ)) / ((k + 1 : ℕ) : ℂ) := by rw [hIH]
          _ = 1 / (((k + 1 + 1) - 1).factorial : ℂ) := by
            rw [show k + 1 + 1 - 1 = k + 1 by omega,
              show k + 1 - 1 = k by omega]
            have hfact : (((k + 1).factorial : ℕ) : ℂ) =
                (((k.factorial : ℕ) : ℂ)) * ((k : ℂ) + 1) := by
              rw [Nat.factorial_succ k]
              push_cast
              ring
            rw [hfact]
            have hk' : ((k : ℂ) + 1) ≠ 0 := by
              have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := hk
              push_cast at hk1
              exact hk1
            have hkf : (((k.factorial : ℕ) : ℂ)) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero k
            field_simp
            push_cast
            ring
  have hJa : (∮ w in C(c, ρ), exp w / w ^ a) = J a := by
    dsimp only [J]
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    simp [div_eq_mul_inv, zpow_neg, zpow_natCast]
  constructor
  · rw [hJa]
    exact hJmain a ha
  · have hcast : ((a - 1 : ℕ) : ℂ) + 1 = (a : ℂ) := by
      have h : ((a - 1) + 1 : ℕ) = a := Nat.sub_add_cancel ha
      exact_mod_cast h
    have hGamma : Gamma (a : ℂ) = ((a - 1).factorial : ℂ) := by
      rw [← hcast]
      exact Complex.Gamma_nat_eq_factorial (a - 1)
    rw [hGamma]
