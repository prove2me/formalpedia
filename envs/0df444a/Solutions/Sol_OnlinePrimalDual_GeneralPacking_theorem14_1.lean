-- Prove2me | solution 1 for OnlinePrimalDual.GeneralPacking.theorem14_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:20:35.25099+00:00
-- url     : https://prove2.me/submissions/b1a78cd9-cc86-45d2-92df-014b1f7898f5

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

theorem aux_t141_weak_duality {I J : Type*} [Fintype I] [Fintype J]
    (inst : GeneralInstance I J)
    (x : I → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i)
    (h_feasible : ∀ j, 1 ≤ ∑ i, inst.a i j * x i)
    (y'' : J → ℝ) (hy'' : ∀ j, 0 ≤ y'' j)
    (hdual : ∀ i, ∑ k, inst.a i k * y'' k ≤ inst.c i) :
    ∑ j, y'' j ≤ ∑ i, inst.c i * x i := by
  calc ∑ j, y'' j ≤ ∑ j, y'' j * ∑ i, inst.a i j * x i := by
        apply Finset.sum_le_sum
        intro j _
        have := mul_le_mul_of_nonneg_left (h_feasible j) (hy'' j)
        simpa using this
    _ = ∑ i, x i * ∑ j, inst.a i j * y'' j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ ∑ i, x i * inst.c i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hdual i) (hx_nonneg i)
    _ = ∑ i, inst.c i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring

end OnlinePrimalDual.GeneralPacking

open OnlinePrimalDual.GeneralPacking

theorem solution {I J : Type*} [Fintype I] [Fintype J] [Nonempty J] [DecidableEq J]
    (inst : GeneralInstance I J) (B : ℝ) (hB : 0 < B)
    (x : I → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (y : J → ℝ) (hy_nonneg : ∀ j, 0 ≤ y j)
    (hX_le_BY : ∑ i, inst.c i * x i ≤ B * ∑ j, y j)
    (h_feasible : ∀ j, 1 ≤ ∑ i, inst.a i j * x i) :
    ∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, ∑ k, inst.a i k * y'' k ≤ inst.c i) →
        ∑ j, y'' j ≤ B * ∑ j, y j := by
  intro y'' hy'' hdual
  exact le_trans (aux_t141_weak_duality inst x hx_nonneg h_feasible y'' hy'' hdual) hX_le_BY
