-- Prove2me | solution 1 for WeierstrassEllipticZeta.box_volume_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T04:46:47.665336+00:00
-- url     : https://prove2.me/submissions/3a659283-225b-4b4e-91bc-d27dce807938

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

theorem solution
    (σ : Type*) [Fintype σ] [DecidableEq σ] (b a : σ → ℕ)
    (hfit : ∀ i : σ, a i ≤ b i) :
    (∏ i : σ, (b i + 1)) ≤ (∏ i : σ, (b i - a i + 1)) +
      ∑ i : σ, a i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b j + 1) := by
  have hprod (s : Finset σ) (x y : σ → ℕ) :
      (∏ i ∈ s, (x i + y i)) ≤ (∏ i ∈ s, x i) +
        ∑ i ∈ s, y i * ∏ j ∈ s.erase i, (x j + y j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      have hfaces :
          (∑ i ∈ insert k s, y i * ∏ j ∈ (insert k s).erase i, (x j + y j)) =
            y k * (∏ j ∈ s, (x j + y j)) +
              (x k + y k) * ∑ i ∈ s, y i * ∏ j ∈ s.erase i, (x j + y j) := by
        rw [Finset.sum_insert hk, Finset.erase_insert hk, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hki : k ≠ i := fun h => hk (h ▸ hi)
        rw [Finset.erase_insert_of_ne hki, Finset.prod_insert]
        · ring
        · exact fun h => hk (Finset.mem_of_mem_erase h)
      rw [Finset.prod_insert hk, Finset.prod_insert hk, hfaces]
      let P := ∏ i ∈ s, (x i + y i)
      let Q := ∏ i ∈ s, x i
      let F := ∑ i ∈ s, y i * ∏ j ∈ s.erase i, (x j + y j)
      change (x k + y k) * P ≤ x k * Q + (y k * P + (x k + y k) * F)
      have hi : P ≤ Q + F := ih
      calc
        (x k + y k) * P = x k * P + y k * P := by ring
        _ ≤ x k * (Q + F) + y k * P :=
          add_le_add (Nat.mul_le_mul_left (x k) hi) le_rfl
        _ = x k * Q + x k * F + y k * P := by ring
        _ ≤ x k * Q + (x k + y k) * F + y k * P := by
          exact add_le_add (add_le_add le_rfl
            (Nat.mul_le_mul_right F (Nat.le_add_right (x k) (y k)))) le_rfl
        _ = x k * Q + (y k * P + (x k + y k) * F) := by ring
  have hexpand (i : σ) : (b i - a i + 1) + a i = b i + 1 := by
    have hi := hfit i
    omega
  simpa only [hexpand] using
    hprod Finset.univ (fun i => b i - a i + 1) a
