-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.second_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:48:22.918996+00:00
-- url     : https://prove2.me/submissions/eb5c2e68-55aa-4eb8-9e62-f142c91857f9

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

set_option autoImplicit false
open SlowConvergence.SteepestDescent

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

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) (mu τ α k),
      |iteratedDeriv 2 (p τ α k) t| ≤ 1 + 150 * |phi τ α k| ∧
        |iteratedDeriv 2 (p τ α k) t| ≤ 1 + 150 * max 1 αhi / αlo := by
  intro t ht
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hα0 : 0 < α k := lt_of_lt_of_le hlo (hα k).1
  have hη : 0 < SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  set e : ℝ := 1 / 2 + SlowConvergence.Newton.eta τ with he
  set q : ℝ := (1 / ((k : ℝ) + 1)) ^ e with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hmu : mu τ α k = α k * q := by
    simp [mu, sk, xk, hq, he]
  have hμ : 0 < mu τ α k := by rw [hmu]; positivity
  have hp : p τ α k = fun t : ℝ => ((α k * (1 - 1 / 2 * α k) * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ))) + (-q) * t + 1 / 2 * t ^ 2
      + (-4 * phi τ α k / mu τ α k) * t ^ 3 + (7 * phi τ α k / mu τ α k ^ 2) * t ^ 4
      + (-3 * phi τ α k / mu τ α k ^ 3) * t ^ 5 := by
    funext t
    simp only [p]
    rfl
  have hpp : |iteratedDeriv 2 (p τ α k) t| ≤ 1 + 9 * |phi τ α k| := by
    rw [hp, scs_poly_dd]
    exact scs_pp_bound _ _ _ hμ ht.1 ht.2
  have hψ0 : 0 < psi τ k := by
    unfold psi
    exact Real.rpow_pos_of_pos (by positivity) _
  have hψ1 : psi τ k < 1 := by
    unfold psi
    exact Real.rpow_lt_one (by positivity) (by rw [div_lt_one (by positivity)]; linarith) (by linarith)
  set m : ℝ := max 1 αhi with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmα : α k ≤ m := le_trans (hα k).2 (le_max_right _ _)
  have hφ : |phi τ α k| ≤ m / αlo := by
    unfold phi
    have habs : |1 - α k - psi τ k| ≤ m := by
      rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hα0)]
    calc 1 / α k * |1 - α k - psi τ k| ≤ 1 / α k * m :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = m / α k := by ring
      _ ≤ m / αlo := div_le_div_of_nonneg_left (by linarith) hlo (hα k).1
  refine ⟨?_, ?_⟩
  · nlinarith [abs_nonneg (phi τ α k)]
  · have : 150 * m / αlo = 150 * (m / αlo) := by ring
    rw [this]
    nlinarith [abs_nonneg (phi τ α k)]
