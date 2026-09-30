-- Prove2me | solution 1 for RevenueManagement.cournot_linear_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:35.166838+00:00
-- url     : https://prove2.me/submissions/5d06a2c4-e178-4e09-b28d-8681302ddc4e

import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

open Finset

end RevenueManagement

open RevenueManagement
theorem solution {n : ℕ} (a c : ℝ) (hac : c < a) :
    (∀ (i : Fin n) (xi : ℝ), 0 ≤ xi →
      cournotPayoff a c (Function.update (fun _ => (a - c) / (n + 1)) i xi) i ≤
        cournotPayoff a c (fun _ => (a - c) / (n + 1)) i) ∧
    a - n * ((a - c) / (n + 1)) = c + (a - c) / (n + 1) := by
  set s := (a - c) / ((n : ℝ) + 1) with hs
  have hns : (n : ℝ) * s = a - c - s := by rw [hs]; field_simp; ring
  constructor
  · intro i xi hxi
    have hn : 0 < n := i.pos
    unfold cournotPayoff
    dsimp only
    rw [Function.update_self,
      Finset.sum_update_of_mem (Finset.mem_univ i) (fun _ => s) xi,
      Finset.sdiff_singleton_eq_erase, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have key : xi * (a - (xi + ((n:ℝ) - 1) * s)) - c * xi
        ≤ s * (a - s - ((n:ℝ) - 1) * s) - c * s := by
      have expand : ∀ z : ℝ,
          z * (a - (z + ((n:ℝ) - 1) * s)) - c * z
            = -(z - s)^2 + (s * (a - s - ((n:ℝ) - 1) * s) - c * s) := by
        intro z
        linear_combination (s - z) * hns
      rw [expand xi]
      nlinarith [sq_nonneg (xi - s)]
    have hgoal : s * (a - (n:ℝ) * s) - c * s = s * (a - s - ((n:ℝ) - 1) * s) - c * s := by ring
    rw [hgoal]
    exact key
  · rw [hs]; field_simp; ring

