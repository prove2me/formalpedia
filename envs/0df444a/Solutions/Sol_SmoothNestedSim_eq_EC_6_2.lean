-- Prove2me | solution 1 for SmoothNestedSim.eq_EC_6_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:07:39.838698+00:00
-- url     : https://prove2.me/submissions/c9f4a9d9-1add-4209-b866-b8e2238b06df

import Mathlib
import Definitions.Def_SmoothNestedSim_matern
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_rkhsNorm

open SmoothNestedSim in
theorem solution {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩb : Bornology.IsBounded Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω) :
    ∀ x ∈ Ω, |f x| ≤ rkhsNorm (maternKernel ν ℓ) Ω f * matern ν ℓ (0 : EuclideanSpace ℝ (Fin d)) := by
  intro x hx
  have hm0 : matern ν ℓ (0 : EuclideanSpace ℝ (Fin d)) = 1 := by
    unfold matern
    rw [if_pos rfl]
  rw [hm0, mul_one]
  obtain ⟨C0, hC0⟩ := hf
  have hle : f x ^ 2 ≤ sInf {C | IsRKHSBound (maternKernel ν ℓ) Ω f C} := by
    refine le_csInf ⟨C0, hC0⟩ (fun C hC => ?_)
    have h := hC.2 1 (fun _ => 1) (fun _ => x) (fun _ => hx)
    have hk : maternKernel ν ℓ x x = 1 := by
      unfold maternKernel
      rw [sub_self, hm0]
    simp only [Fin.sum_univ_one, one_mul, hk, mul_one] at h
    exact h
  unfold rkhsNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hle
