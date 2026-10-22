-- Prove2me | solution 1 for SlowConvergence.Newton.p_second_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:28:02.761494+00:00
-- url     : https://prove2.me/submissions/27158462-8c78-44bb-9db3-eb25dbfbe3c4

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false

theorem scs_poly_d (A B C D E t : ℝ) :
    HasDerivAt (fun t : ℝ => A + B * t + 1 / 2 * t ^ 2 + C * t ^ 3 + D * t ^ 4 + E * t ^ 5)
      (B + t + 3 * C * t ^ 2 + 4 * D * t ^ 3 + 5 * E * t ^ 4) t := by
  have h := ((((((hasDerivAt_const t A).fun_add ((hasDerivAt_id t).const_mul B)).fun_add
    ((hasDerivAt_pow 2 t).const_mul (1 / 2))).fun_add ((hasDerivAt_pow 3 t).const_mul C)).fun_add
    ((hasDerivAt_pow 4 t).const_mul D)).fun_add ((hasDerivAt_pow 5 t).const_mul E))
  refine h.congr_deriv ?_
  simp; ring

theorem scs_poly_d2 (B C D E t : ℝ) :
    HasDerivAt (fun t : ℝ => B + t + 3 * C * t ^ 2 + 4 * D * t ^ 3 + 5 * E * t ^ 4)
      (1 + 6 * C * t + 12 * D * t ^ 2 + 20 * E * t ^ 3) t := by
  have h := (((((hasDerivAt_const t B).fun_add (hasDerivAt_id t)).fun_add
    ((hasDerivAt_pow 2 t).const_mul (3 * C))).fun_add ((hasDerivAt_pow 3 t).const_mul (4 * D))).fun_add
    ((hasDerivAt_pow 4 t).const_mul (5 * E)))
  refine h.congr_deriv ?_
  simp; ring

theorem scs_poly_dd (A B C D E t : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => A + B * t + 1 / 2 * t ^ 2 + C * t ^ 3 + D * t ^ 4 + E * t ^ 5) t
      = 1 + 6 * C * t + 12 * D * t ^ 2 + 20 * E * t ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (fun t : ℝ => A + B * t + 1 / 2 * t ^ 2 + C * t ^ 3 + D * t ^ 4 + E * t ^ 5)
      = fun t => B + t + 3 * C * t ^ 2 + 4 * D * t ^ 3 + 5 * E * t ^ 4 :=
    funext fun t => (scs_poly_d A B C D E t).deriv
  rw [this]
  exact (scs_poly_d2 B C D E t).deriv

theorem scs_g_bound (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |-24 * u + 84 * u ^ 2 - 60 * u ^ 3| ≤ 9 := by
  have e : -24 * u + 84 * u ^ 2 - 60 * u ^ 3 = -(12 * (u * (1 - u)) * (2 - 5 * u)) := by ring
  have hA : 0 ≤ u * (1 - u) := mul_nonneg h0 (by linarith)
  have hB : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hC : |2 - 5 * u| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  calc 12 * (u * (1 - u)) * |2 - 5 * u| ≤ 12 * (1 / 4) * 3 := by
        apply mul_le_mul (by linarith) hC (abs_nonneg _) (by norm_num)
    _ = 9 := by norm_num

theorem scs_pp_bound (μ φ t : ℝ) (hμ : 0 < μ) (h0 : 0 ≤ t) (h1 : t ≤ μ) :
    |1 + 6 * (-4 * φ / μ) * t + 12 * (7 * φ / μ ^ 2) * t ^ 2 + 20 * (-3 * φ / μ ^ 3) * t ^ 3|
      ≤ 1 + 9 * |φ| := by
  have hu0 : 0 ≤ t / μ := div_nonneg h0 hμ.le
  have hu1 : t / μ ≤ 1 := (div_le_one hμ).mpr h1
  have e : 1 + 6 * (-4 * φ / μ) * t + 12 * (7 * φ / μ ^ 2) * t ^ 2 + 20 * (-3 * φ / μ ^ 3) * t ^ 3
      = 1 + φ * (-24 * (t / μ) + 84 * (t / μ) ^ 2 - 60 * (t / μ) ^ 3) := by
    field_simp
    ring
  rw [e]
  calc |1 + φ * (-24 * (t / μ) + 84 * (t / μ) ^ 2 - 60 * (t / μ) ^ 3)|
      ≤ |1| + |φ * (-24 * (t / μ) + 84 * (t / μ) ^ 2 - 60 * (t / μ) ^ 3)| := abs_add_le _ _
    _ ≤ 1 + 9 * |φ| := by
      rw [abs_mul, abs_one]
      have := scs_g_bound (t / μ) hu0 hu1
      nlinarith [abs_nonneg φ]


theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    (∀ t ∈ Set.Icc (0 : ℝ) (SlowConvergence.Newton.mu τ k),
        |deriv (deriv (SlowConvergence.Newton.p τ k)) t|
          ≤ 1 + 150 * |SlowConvergence.Newton.phi τ k|) ∧
      1 + 150 * |SlowConvergence.Newton.phi τ k| ≤ 151 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hη : 0 < SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  have hψ0 : 0 < SlowConvergence.SteepestDescent.psi τ k := by
    unfold SlowConvergence.SteepestDescent.psi
    exact Real.rpow_pos_of_pos (by positivity) _
  have hψ1 : SlowConvergence.SteepestDescent.psi τ k < 1 := by
    unfold SlowConvergence.SteepestDescent.psi
    exact Real.rpow_lt_one (by positivity) (by rw [div_lt_one (by positivity)]; linarith) (by linarith)
  have hphi : |SlowConvergence.Newton.phi τ k| < 1 := by
    unfold SlowConvergence.Newton.phi
    rw [abs_neg, abs_of_pos hψ0]; exact hψ1
  have hμ : 0 < SlowConvergence.Newton.mu τ k := by
    unfold SlowConvergence.Newton.mu
    exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨?_, by linarith⟩
  intro t ht
  have hp : SlowConvergence.Newton.p τ k = fun t : ℝ =>
      (1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ))
        + (-SlowConvergence.Newton.mu τ k) * t + 1 / 2 * t ^ 2
        + (-4 * SlowConvergence.Newton.phi τ k / SlowConvergence.Newton.mu τ k) * t ^ 3
        + (7 * SlowConvergence.Newton.phi τ k / SlowConvergence.Newton.mu τ k ^ 2) * t ^ 4
        + (-3 * SlowConvergence.Newton.phi τ k / SlowConvergence.Newton.mu τ k ^ 3) * t ^ 5 := by
    funext t
    rfl
  have hdd : deriv (deriv (SlowConvergence.Newton.p τ k)) t
      = iteratedDeriv 2 (SlowConvergence.Newton.p τ k) t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hdd, hp, scs_poly_dd]
  calc _ ≤ 1 + 9 * |SlowConvergence.Newton.phi τ k| := scs_pp_bound _ _ _ hμ ht.1 ht.2
    _ ≤ 1 + 150 * |SlowConvergence.Newton.phi τ k| := by
      nlinarith [abs_nonneg (SlowConvergence.Newton.phi τ k)]
