-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:34:41.311728+00:00
-- url     : https://prove2.me/submissions/43441e27-c12e-49e3-9131-02da86e72981

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

open TokenQueue.ProductForm Finset

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hk : KPos P) (l : List T) (t : T) (hl : (t :: l).Nodup)
    (n : ℕ → ℕ) (hn : n 0 = 0) :
    ∑ k ∈ range (l.length + 1),
      (kfun P (l.take k ++ [t]) - kfun P (l.take k)) / kfun P (l.take k ++ [t]) *
        (∏ j ∈ Icc (k + 1) l.length, (kfun P (l.take j) / kfun P (l.take j ++ [t])) ^ (n j + 1)) *
        ∑ m ∈ range (n k + 1), (kfun P (l.take k) / kfun P (l.take k ++ [t])) ^ m = 1 := by
  set a : ℕ → ℝ := fun j => kfun P (l.take j) / kfun P (l.take j ++ [t]) with ha
  have hpos : ∀ k, 0 < kfun P (l.take k ++ [t]) := by
    intro k
    apply hk
    · rw [List.nodup_append]
      refine ⟨(List.nodup_cons.mp hl).2.sublist (List.take_sublist _ _), List.nodup_singleton t, ?_⟩
      intro u hu v hv huv
      simp only [List.mem_singleton] at hv
      subst hv; subst huv
      exact (List.nodup_cons.mp hl).1 (List.mem_of_mem_take hu)
    · simp
  have h0 : a 0 = 0 := by simp [ha, kfun]
  -- P k = ∏_{j ∈ Icc k i} a_j^(n_j+1)
  set Q : ℕ → ℝ := fun k => ∏ j ∈ Icc k l.length, a j ^ (n j + 1) with hQ
  have hterm : ∀ k ∈ range (l.length + 1),
      (kfun P (l.take k ++ [t]) - kfun P (l.take k)) / kfun P (l.take k ++ [t]) *
        (∏ j ∈ Icc (k + 1) l.length, (kfun P (l.take j) / kfun P (l.take j ++ [t])) ^ (n j + 1)) *
        ∑ m ∈ range (n k + 1), (kfun P (l.take k) / kfun P (l.take k ++ [t])) ^ m
        = Q (k + 1) - Q k := by
    intro k hk'
    simp only [mem_range] at hk'
    have hsplit : Q k = a k ^ (n k + 1) * Q (k + 1) := by
      simp only [hQ]
      rw [← Finset.mul_prod_Ioc_eq_prod_Icc (by omega : k ≤ l.length), Finset.Icc_add_one_left_eq_Ioc]
    have h1 : (kfun P (l.take k ++ [t]) - kfun P (l.take k)) / kfun P (l.take k ++ [t])
        = 1 - a k := by
      simp only [ha]; field_simp [(hpos k).ne']
    rw [hsplit, h1]
    change (1 - a k) * Q (k + 1) * ∑ m ∈ range (n k + 1), a k ^ m = _
    have hgeom : (1 - a k) * ∑ m ∈ range (n k + 1), a k ^ m = 1 - a k ^ (n k + 1) := by
      rw [mul_comm]; exact geom_sum_mul_neg (a k) (n k + 1)
    linear_combination Q (k + 1) * hgeom
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun k => Q k)]
  have hQ0 : Q 0 = 0 := by
    simp only [hQ]
    apply Finset.prod_eq_zero (i := 0) (by simp)
    rw [h0]; simp
  have hQe : Q (l.length + 1) = 1 := by
    simp only [hQ]; rw [Finset.Icc_eq_empty (by omega)]; simp
  rw [hQ0, hQe]; ring
