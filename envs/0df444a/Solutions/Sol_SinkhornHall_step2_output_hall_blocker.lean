-- Prove2me | solution 1 for SinkhornHall.step2_output_hall_blocker
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:00:05.447292+00:00
-- url     : https://prove2.me/submissions/3b69dc58-b504-4236-80b3-bac48b446b91

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

open SinkhornHall in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hedge : ∀ i j, 0 < A i j → x i * y j < ((∏ i', x i') * ∏ j', y j') ^ ((1 : ℝ) / n))
    (σ τ : Equiv.Perm (Fin n)) (k : Fin n) (hσ : Antitone (x ∘ σ)) (hτ : Monotone (y ∘ τ))
    (hk : (∏ i, x i) * (∏ j, y j) ≤ (x (σ k) * y (τ k)) ^ n) :
    Gamma A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ) ⊆
        (Finset.univ.filter (fun t : Fin n => t < k)).image τ ∧
      IsHallBlocker A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact k.elim0
  have hG : 0 ≤ (∏ i, x i) * (∏ j, y j) :=
    mul_nonneg (Finset.prod_nonneg fun i _ => (hx i).le) (Finset.prod_nonneg fun j _ => (hy j).le)
  have ha : 0 ≤ x (σ k) * y (τ k) := (mul_pos (hx _) (hy _)).le
  have hroot : ((∏ i, x i) * (∏ j, y j)) ^ ((1 : ℝ) / n) ≤ x (σ k) * y (τ k) := by
    calc ((∏ i, x i) * (∏ j, y j)) ^ ((1 : ℝ) / n)
        ≤ ((x (σ k) * y (τ k)) ^ n) ^ ((1 : ℝ) / n) :=
          Real.rpow_le_rpow hG hk (by positivity)
      _ = x (σ k) * y (τ k) := by rw [one_div, Real.pow_rpow_inv_natCast ha hn]
  have hsub : Gamma A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ) ⊆
      (Finset.univ.filter (fun t : Fin n => t < k)).image τ := by
    intro j hj
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨i, hi, hpos⟩ := hj
    rw [mem_image] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    rw [mem_filter] at ht
    have hxi : x (σ k) ≤ x (σ t) := hσ ht.2
    have h1 := hedge (σ t) j hpos
    have hyj : y j < y (τ k) := by
      by_contra hc
      push_neg at hc
      have : x (σ k) * y (τ k) ≤ x (σ t) * y j := mul_le_mul hxi hc (hy _).le (hx _).le
      linarith
    rw [mem_image]
    refine ⟨τ.symm j, ?_, by simp⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    by_contra hc
    push_neg at hc
    have h2 := hτ hc
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h2
    linarith
  refine ⟨hsub, ?_⟩
  unfold IsHallBlocker
  have c1 : (Finset.univ.filter (fun t : Fin n => t < k)) = Iio k := by
    ext t
    simp
  have c2 : (Finset.univ.filter (fun t : Fin n => t ≤ k)) = Iic k := by
    ext t
    simp
  calc (Gamma A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ)).card
      ≤ ((Finset.univ.filter (fun t : Fin n => t < k)).image τ).card := card_le_card hsub
    _ ≤ (Finset.univ.filter (fun t : Fin n => t < k)).card := card_image_le
    _ = (k : ℕ) := by rw [c1, Fin.card_Iio]
    _ < (k : ℕ) + 1 := Nat.lt_succ_self _
    _ = (Finset.univ.filter (fun t : Fin n => t ≤ k)).card := by rw [c2, Fin.card_Iic]
    _ = ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ).card :=
        (card_image_of_injective _ σ.injective).symm
