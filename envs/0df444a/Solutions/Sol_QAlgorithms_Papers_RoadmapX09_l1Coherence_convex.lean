-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapX09.l1Coherence_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:58:05.828983+00:00
-- url     : https://prove2.me/submissions/83946b4c-3fb0-46be-a487-c8235aa0c970

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
set_option autoImplicit false

open QAlgorithms

theorem solution (d m : ℕ) (hd : 1 ≤ d)
    (p : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a))
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    (∑ a, p a * Coherence.l1Coherence (rho a)) ≥
      Coherence.l1Coherence (∑ a, (p a : ℂ) • rho a) := by
  classical
  unfold Coherence.l1Coherence
  calc
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
        ‖(∑ a, (p a : ℂ) • rho a) i j‖) ≤
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
          ∑ a, p a * ‖rho a i j‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      calc
        ‖∑ a, (p a : ℂ) * rho a i j‖ ≤ ∑ a, ‖(p a : ℂ) * rho a i j‖ :=
          norm_sum_le _ _
        _ = ∑ a, p a * ‖rho a i j‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    _ = ∑ a, p a * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho a i j‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext i
      rw [Finset.sum_comm]

#print axioms solution
