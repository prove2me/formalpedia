-- Prove2me | solution 1 for SlowConvergence.Newton.hermite_p_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:27:10.023487+00:00
-- url     : https://prove2.me/submissions/5616a96a-f8d4-400f-9a00-f1ee6bcee002

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace
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

theorem scs_alg0 (c0 B m φ : ℝ) (hm : m ≠ 0) :
    c0 + B * m + 1 / 2 * m ^ 2 + (-4 * φ / m) * m ^ 3 + (7 * φ / m ^ 2) * m ^ 4
      + (-3 * φ / m ^ 3) * m ^ 5 = c0 + B * m + 1 / 2 * m ^ 2 := by
  field_simp
  ring

theorem scs_alg1 (B m φ : ℝ) (hm : m ≠ 0) :
    B + m + 3 * (-4 * φ / m) * m ^ 2 + 4 * (7 * φ / m ^ 2) * m ^ 3
      + 5 * (-3 * φ / m ^ 3) * m ^ 4 = B + m + φ * m := by
  field_simp
  ring

theorem scs_alg2 (m φ : ℝ) (hm : m ≠ 0) :
    1 + 6 * (-4 * φ / m) * m + 12 * (7 * φ / m ^ 2) * m ^ 2
      + 20 * (-3 * φ / m ^ 3) * m ^ 3 = 1 := by
  field_simp
  ring

theorem scs_herm (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) (k : ℕ) :
    p τ α k 0 = α k * (1 - 1 / 2 * α k) * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ) ∧
      p τ α k (mu τ α k) = 0 ∧
      deriv (p τ α k) 0 = -((1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      deriv (p τ α k) (mu τ α k) = -((1 / ((k : ℝ) + 2)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      iteratedDeriv 2 (p τ α k) 0 = 1 ∧
      iteratedDeriv 2 (p τ α k) (mu τ α k) = 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hα0 : 0 < α k := lt_of_lt_of_le hlo (hα k).1
  set e : ℝ := 1 / 2 + SlowConvergence.Newton.eta τ with he
  set q : ℝ := (1 / ((k : ℝ) + 1)) ^ e with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hmu : mu τ α k = α k * q := by
    simp [mu, sk, xk, hq, he]
  have hm : mu τ α k ≠ 0 := by rw [hmu]; positivity
  have hc : (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ) = q ^ 2 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [he]; push_cast; ring
  have hp : p τ α k = fun t : ℝ => (α k * (1 - 1 / 2 * α k) * q ^ 2) + (-q) * t + 1 / 2 * t ^ 2
      + (-4 * phi τ α k / mu τ α k) * t ^ 3 + (7 * phi τ α k / mu τ α k ^ 2) * t ^ 4
      + (-3 * phi τ α k / mu τ α k ^ 3) * t ^ 5 := by
    funext t
    simp only [p, hc]
    rfl
  have hφ : phi τ α k * α k = 1 - α k - psi τ k := by
    unfold phi; field_simp
  have hqψ : q * psi τ k = (1 / ((k : ℝ) + 2)) ^ e := by
    rw [hq]; unfold psi
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp, hc]; simp
  · rw [hp]
    beta_reduce
    have := scs_alg0 (α k * (1 - 1 / 2 * α k) * q ^ 2) (-q) (mu τ α k) (phi τ α k) hm
    rw [this, hmu]; ring
  · rw [hp, (scs_poly_d _ _ _ _ _ 0).deriv]; simp
  · rw [hp, (scs_poly_d _ _ _ _ _ _).deriv, scs_alg1 _ _ _ hm, hmu, ← hqψ]
    linear_combination (q) * hφ
  · rw [hp, scs_poly_dd]; simp
  · rw [hp, scs_poly_dd, scs_alg2 _ _ hm]

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    SlowConvergence.Newton.p τ k 0 =
        1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ) ∧
      SlowConvergence.Newton.p τ k (SlowConvergence.Newton.mu τ k) = 0 ∧
      deriv (SlowConvergence.Newton.p τ k) 0 =
        -((1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      deriv (SlowConvergence.Newton.p τ k) (SlowConvergence.Newton.mu τ k) =
        -((1 / ((k : ℝ) + 2)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      deriv (deriv (SlowConvergence.Newton.p τ k)) 0 = 1 ∧
      deriv (deriv (SlowConvergence.Newton.p τ k)) (SlowConvergence.Newton.mu τ k) = 1 := by
  have h := scs_herm τ hτ0 hτ1 1 1 one_pos le_rfl (by norm_num) (fun _ => 1)
    (fun _ => ⟨le_rfl, le_rfl⟩) k
  have hmu : SlowConvergence.SteepestDescent.mu τ (fun _ => (1 : ℝ)) k
      = SlowConvergence.Newton.mu τ k := by
    simp [SlowConvergence.SteepestDescent.mu, SlowConvergence.SteepestDescent.sk,
      SlowConvergence.SteepestDescent.xk, SlowConvergence.Newton.mu]
  have hphi : SlowConvergence.SteepestDescent.phi τ (fun _ => (1 : ℝ)) k
      = SlowConvergence.Newton.phi τ k := by
    simp [SlowConvergence.SteepestDescent.phi, SlowConvergence.Newton.phi]
  have hp : SlowConvergence.SteepestDescent.p τ (fun _ => (1 : ℝ)) k
      = SlowConvergence.Newton.p τ k := by
    funext t
    simp only [SlowConvergence.SteepestDescent.p, SlowConvergence.Newton.p, hmu, hphi,
      SlowConvergence.Newton.mu]
    ring
  have hdd : ∀ x : ℝ, iteratedDeriv 2 (SlowConvergence.Newton.p τ k) x
      = deriv (deriv (SlowConvergence.Newton.p τ k)) x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hmu, hp] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [hdd] at h5 h6
  refine ⟨?_, h2, h3, h4, h5, h6⟩
  rw [h1]
  norm_num
