-- Prove2me | solution 1 for SupplyChainTheory.ar1_moments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:49:33.122172+00:00
-- url     : https://prove2.me/submissions/2f4e977a-3d7b-4f0f-8423-4c9dc56d1f58

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section AR1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma ar1_rho_sq (X : AR1Demand P) : X.rho ^ 2 < 1 := by
  have h := X.rho_lt
  have h2 : |X.rho| ^ 2 < 1 := by
    have h0 := abs_nonneg X.rho
    nlinarith
  rwa [sq_abs] at h2

lemma ar1_memLp (X : AR1Demand P) (t : ℤ) : MemLp (X.D t) 2 P := by
  have h := memLp_id_gaussianReal' (μ := X.d / (1 - X.rho))
    (v := Real.toNNReal (X.sigma ^ 2 / (1 - X.rho ^ 2))) 2 (by norm_num)
  rw [← X.stationary t] at h
  exact (memLp_map_measure_iff h.aestronglyMeasurable (X.measurable_D t).aemeasurable).mp h

lemma ar1_mean (X : AR1Demand P) (t : ℤ) : ∫ ω, X.D t ω ∂P = X.d / (1 - X.rho) := by
  have h := integral_map (μ := P) (X.measurable_D t).aemeasurable
    (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [← h, X.stationary t, integral_id_gaussianReal]

lemma ar1_var (X : AR1Demand P) (t : ℤ) :
    variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by
  have h := variance_map (X := id) (μ := P) (Y := X.D t) aemeasurable_id
    (X.measurable_D t).aemeasurable
  rw [X.stationary t, variance_id_gaussianReal] at h
  have hpos : 0 ≤ X.sigma ^ 2 / (1 - X.rho ^ 2) :=
    div_nonneg (sq_nonneg _) (by linarith [ar1_rho_sq X])
  rw [Real.coe_toNNReal _ hpos] at h
  exact h.symm

lemma ar1_eps_memLp (X : AR1Demand P) (t : ℤ) : MemLp (X.eps t) 2 P := by
  have he : X.eps t = fun ω => X.D t ω - X.d - X.rho * X.D (t - 1) ω := by
    funext ω; rw [X.recursion t ω]; ring
  rw [he]
  exact ((ar1_memLp X t).sub (memLp_const _)).sub ((ar1_memLp X (t - 1)).const_mul _)

lemma ar1_cov (X : AR1Demand P) : ∀ (k : ℕ) (t : ℤ),
    covariance (X.D t) (X.D (t - k)) P = X.rho ^ k * (X.sigma ^ 2 / (1 - X.rho ^ 2)) := by
  intro k
  induction k with
  | zero =>
    intro t
    simp only [Nat.cast_zero, sub_zero, pow_zero, one_mul]
    rw [covariance_self (X.measurable_D t).aemeasurable, ar1_var]
  | succ k ih =>
    intro t
    have e1 : t - ((k + 1 : ℕ) : ℤ) = (t - 1) - k := by push_cast; ring
    rw [e1]
    set Y := X.D (t - 1 - k) with hY
    have hind : IndepFun (X.eps t) Y P :=
      (X.eps_indep_past t).comp measurable_id (measurable_pi_apply k)
    have hfun : X.D t = fun ω => X.d + ((fun ω => X.rho * X.D (t - 1) ω) + X.eps t) ω := by
      funext ω; simp only [Pi.add_apply]; rw [X.recursion t ω]; ring
    have hm1 : MemLp (fun ω => X.rho * X.D (t - 1) ω) 2 P := (ar1_memLp X (t - 1)).const_mul _
    have hint : Integrable ((fun ω => X.rho * X.D (t - 1) ω) + X.eps t) P :=
      (hm1.add (ar1_eps_memLp X t)).integrable (by norm_num)
    rw [hfun, covariance_const_add_left hint,
      covariance_add_left hm1 (ar1_eps_memLp X t) (ar1_memLp X _),
      covariance_const_mul_left, hind.covariance_eq_zero (ar1_eps_memLp X t) (ar1_memLp X _),
      ih (t - 1)]
    ring

theorem ar1_main (X : AR1Demand P) (t : ℤ) (k : ℕ) :
    (∫ ω, X.D t ω ∂P) = X.d / (1 - X.rho)
      ∧ variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2)
      ∧ covariance (X.D t) (X.D (t - k)) P = X.rho ^ k * variance (X.D t) P := by
  refine ⟨ar1_mean X t, ar1_var X t, ?_⟩
  rw [ar1_cov X k t, ar1_var X t]

theorem demand_part_main (X : AR1Demand P) (L m : ℕ) (hm : 0 < m) (t : ℤ) :
    variance
        (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) P
      = (1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m))
          * variance (X.D t) P := by
  have hA : MemLp (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω) 2 P :=
    (ar1_memLp X (t - 1)).const_mul _
  have hB : MemLp (fun ω => ((L : ℝ) / m) * X.D (t - m - 1) ω) 2 P :=
    (ar1_memLp X (t - m - 1)).const_mul _
  have e1 : t - (m : ℤ) - 1 = (t - 1) - m := by ring
  have hcov := ar1_cov X m (t - 1)
  rw [← e1] at hcov
  rw [variance_fun_sub hA hB, variance_const_mul, variance_const_mul, covariance_const_mul_left,
    covariance_const_mul_right, hcov, ar1_var X (t - 1), ar1_var X (t - m - 1), ar1_var X t]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

end AR1

end SupplyChainTheory

open SupplyChainTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (t : ℤ) (k : ℕ) :
    (∫ ω, X.D t ω ∂P) = X.d / (1 - X.rho)
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2)
      ∧ ProbabilityTheory.covariance (X.D t) (X.D (t - k)) P
          = X.rho ^ k * ProbabilityTheory.variance (X.D t) P := by
  exact ar1_main X t k
