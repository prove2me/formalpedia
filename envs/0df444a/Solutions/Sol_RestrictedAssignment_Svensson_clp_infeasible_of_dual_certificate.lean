-- Prove2me | solution 1 for RestrictedAssignment.Svensson.clp_infeasible_of_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:28:33.895951+00:00
-- url     : https://prove2.me/submissions/5dc64185-b61e-48e2-b1d9-1828a3be6960

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

theorem aux_clpdc_swap {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (S : M → Finset (Finset J)) (x : M → Finset J → ℝ) (z : J → ℝ) :
    ∑ j, z j * ∑ i, ∑ C ∈ (S i).filter (fun C => j ∈ C), x i C
      = ∑ i, ∑ C ∈ S i, x i C * ∑ j ∈ C, z j := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp [mul_comm]

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (y : M → ℝ) (z : J → ℝ)
    (hdual : CLPDualFeasible Γ p T y z) (hneg : ∑ i, y i < ∑ j, z j) :
    ¬ CLPFeasible Γ p T := by
  rintro ⟨x, hx0, hx1, hx2⟩
  obtain ⟨hy, hz, hC⟩ := hdual
  have h1 : ∑ j, z j ≤ ∑ j, z j * ∑ i, ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C), x i C := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := mul_le_mul_of_nonneg_left (hx2 j) (hz j)
    linarith
  rw [aux_clpdc_swap] at h1
  have h2 : ∑ i, ∑ C ∈ configs Γ p T i, x i C * ∑ j ∈ C, z j ≤ ∑ i, y i := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc ∑ C ∈ configs Γ p T i, x i C * ∑ j ∈ C, z j
        ≤ ∑ C ∈ configs Γ p T i, x i C * y i :=
          Finset.sum_le_sum (fun C hCm => mul_le_mul_of_nonneg_left (hC i C hCm) (hx0 i C))
      _ = (∑ C ∈ configs Γ p T i, x i C) * y i := by rw [Finset.sum_mul]
      _ ≤ 1 * y i := mul_le_mul_of_nonneg_right (hx1 i) (hy i)
      _ = y i := one_mul _
  linarith
