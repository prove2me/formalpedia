-- Prove2me | solution 1 for SubSuperStoch.SubSpec.chain_rowSum_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:30:33.208182+00:00
-- url     : https://prove2.me/submissions/f04552a3-e663-45b4-b69d-df9ad658c5ac

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

set_option autoImplicit false

open SubSuperStoch.SubSpec

theorem rs_mul_aux {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowSum (F * G) i = ∑ m, F i m * rowSum G m := by
  simp only [rowSum, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem pow_nonneg_aux {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : ∀ i j, 0 ≤ F i j) :
    ∀ k i j, 0 ≤ (F ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hF _ _) (ih _ _))

theorem rs_pow_le_one {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F) :
    ∀ k m, rowSum (F ^ k) m ≤ 1 := by
  intro k
  induction k with
  | zero => intro m; simp [rowSum, Matrix.one_apply]
  | succ k ih =>
    intro m
    rw [pow_succ', rs_mul_aux]
    calc ∑ j, F m j * rowSum (F ^ k) j ≤ ∑ j, F m j * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (hF.1 _ _))
      _ = rowSum F m := by simp [rowSum]
      _ ≤ 1 := hF.2 m

theorem solution {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (i : Fin n) (hi : rowSum F i < 1)
    (c : ℕ → Fin n) (L : ℕ) (hc0 : c 0 = i) (hL : 1 ≤ L) (hc : IsChain F c L) :
    rowSum (F ^ (L + 1)) (c L) ≤ 1 - (1 - α₁) * α₂ ^ L ∧ 1 - (1 - α₁) * α₂ ^ L < 1 := by
  have hα1lt : α₁ < 1 := by
    obtain ⟨s, hs, hs'⟩ := hα₁.1
    rw [hs']; exact hs
  have hα2pos : 0 < α₂ := by
    obtain ⟨a, b, hab, h⟩ := hα₂.1
    rw [h]; exact hab
  have hδ : ∀ t : ℕ, 0 ≤ (1 - α₁) * α₂ ^ t := fun t =>
    mul_nonneg (by linarith) (pow_nonneg hα2pos.le t)
  have key : ∀ t, t ≤ L → rowSum (F ^ (t + 1)) (c t) ≤ 1 - (1 - α₁) * α₂ ^ t := by
    intro t
    induction t with
    | zero =>
      intro _
      have : rowSum F i ≤ α₁ := hα₁.2 ⟨i, hi, rfl⟩
      simp only [pow_zero, mul_one, zero_add, pow_one, hc0]
      linarith
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hch := (hc t (by omega)).1
      have hFpos : 0 < F (c (t + 1)) (c t) := lt_of_le_of_ne (hF.1 _ _) (Ne.symm hch)
      have hge : α₂ ≤ F (c (t + 1)) (c t) := hα₂.2 ⟨_, _, hFpos, rfl⟩
      set R : Fin n → ℝ := fun m => rowSum (F ^ (t + 1)) m with hR
      set f : Fin n → ℝ := fun m => F (c (t + 1)) m with hf
      have hR1 : ∀ m, R m ≤ 1 := fun m => rs_pow_le_one F hF _ m
      have hsum : ∑ m, f m * R m = ∑ m, f m - ∑ m, f m * (1 - R m) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have hterm : f (c t) * (1 - R (c t)) ≤ ∑ m, f m * (1 - R m) :=
        Finset.single_le_sum (f := fun m => f m * (1 - R m))
          (fun m _ => mul_nonneg (hF.1 _ _) (by linarith [hR1 m])) (Finset.mem_univ _)
      have hrs : ∑ m, f m ≤ 1 := by
        have := hF.2 (c (t + 1)); simpa [rowSum, hf] using this
      have hRt : R (c t) ≤ 1 - (1 - α₁) * α₂ ^ t := ih'
      have h1 : (1 - α₁) * α₂ ^ t ≤ 1 - R (c t) := by linarith
      have h2 : α₂ * ((1 - α₁) * α₂ ^ t) ≤ f (c t) * (1 - R (c t)) :=
        mul_le_mul hge h1 (hδ t) hFpos.le
      have : rowSum (F ^ (t + 1 + 1)) (c (t + 1)) = ∑ m, f m * R m := by
        rw [pow_succ', rs_mul_aux]
      rw [this, hsum]
      have : α₂ * ((1 - α₁) * α₂ ^ t) = (1 - α₁) * α₂ ^ (t + 1) := by ring
      linarith
  refine ⟨key L le_rfl, ?_⟩
  have : 0 < (1 - α₁) * α₂ ^ L := mul_pos (by linarith) (pow_pos hα2pos L)
  linarith
