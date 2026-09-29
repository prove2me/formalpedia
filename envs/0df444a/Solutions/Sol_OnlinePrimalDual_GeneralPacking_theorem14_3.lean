-- Prove2me | solution 1 for OnlinePrimalDual.GeneralPacking.theorem14_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:20:56.084379+00:00
-- url     : https://prove2.me/submissions/2b0d16cb-0293-4669-a356-5abef91f07ae

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

theorem aux_t143_log_nonneg (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith

end OnlinePrimalDual.GeneralPacking

open OnlinePrimalDual.GeneralPacking

theorem solution {I J : Type*} [Fintype I] [Fintype J]
    (inst : GeneralInstance I J) (B : ℝ) (hB : 0 < B)
    (x : I → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (y : J → ℝ) (hy_nonneg : ∀ j, 0 ≤ y j)
    (hX_le_ratio : ∑ i, inst.c i * x i ≤
        (8 * Real.log (2 * (Fintype.card I : ℝ)) / B) * ∑ j, y j)
    (h_feasible : ∀ j, 1 / B ≤ ∑ i, inst.a i j * x i)
    (hweak_duality : ∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 / B ≤ ∑ i, inst.a i j * x'' i) →
        ∑ j, y j ≤ ∑ i, inst.c i * x'' i) :
    ∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 / B ≤ ∑ i, inst.a i j * x'' i) →
      ∑ i, inst.c i * x i ≤ (8 * Real.log (2 * (Fintype.card I : ℝ)) / B) * ∑ i, inst.c i * x'' i
    := by
  intro x'' hx'' hfeas
  have hr : 0 ≤ 8 * Real.log (2 * (Fintype.card I : ℝ)) / B :=
    div_nonneg (mul_nonneg (by norm_num) (aux_t143_log_nonneg _)) hB.le
  exact hX_le_ratio.trans (mul_le_mul_of_nonneg_left (hweak_duality x'' hx'' hfeas) hr)
