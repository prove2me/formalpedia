-- Prove2me | solution 1 for UniformPrecSched.Makespan.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:39:47.215466+00:00
-- url     : https://prove2.me/submissions/18ed8391-28f3-4729-a4a0-c24973ec1ff0

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

set_option autoImplicit false

namespace UniformPrecSched.Makespan.L32Aux

open UniformPrecSched.Makespan

theorem classSpeed_mem {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    ∃ i, I.s i = classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := by
    unfold classSpeed; exact Finset.orderEmbOfFin_mem _ _ _
  simp only [speedSet, Finset.mem_image, Finset.mem_univ, true_and] at h
  exact h

theorem classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  obtain ⟨i, hi⟩ := classSpeed_mem I κ
  rw [← hi]; exact I.s_pos i

theorem c_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < (classCount I κ : ℝ) * classSpeed I κ := by
  obtain ⟨i, hi⟩ := classSpeed_mem I κ
  have hc : 0 < classCount I κ := by
    unfold classCount
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  exact mul_pos (by exact_mod_cast hc) (classSpeed_pos I κ)

theorem key {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x 2 k) (j : Fin n) :
    I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))) ≤
      2 * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
  obtain ⟨h1, -, -, -, -, h8⟩ := hLP
  set B := badSet I x 2 j with hBdef
  have hpj := I.p_pos j
  have hpbar : 0 < pbar I x j := by
    have hex : ∃ κ, 0 < x κ j := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ κ, x κ j ≤ 0 := Finset.sum_nonpos (fun κ _ => hcon κ)
      linarith [h1 j]
    obtain ⟨κ0, hκ0⟩ := hex
    unfold pbar
    apply Finset.sum_pos' (fun κ _ => mul_nonneg (div_nonneg hpj.le (classSpeed_pos I κ).le) (h8 κ j))
    exact ⟨κ0, Finset.mem_univ _, mul_pos (div_pos hpj (classSpeed_pos I κ0)) hκ0⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (numSpeeds I)))
    (fun κ => κ ∈ B) (fun κ => x κ j)
  have hBle : 2 * pbar I x j * ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), x κ j ≤ pbar I x j := by
    rw [Finset.mul_sum]
    calc ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), 2 * pbar I x j * x κ j
        ≤ ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), I.p j / classSpeed I κ * x κ j := by
          apply Finset.sum_le_sum
          intro κ hκ
          have hm : κ ∈ B := (Finset.mem_filter.mp hκ).2
          have : 2 * pbar I x j < I.p j / classSpeed I κ := by
            simpa [hBdef, badSet] using hm
          exact mul_le_mul_of_nonneg_right this.le (h8 κ j)
      _ ≤ ∑ κ, I.p j / classSpeed I κ * x κ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro κ _ _
          exact mul_nonneg (div_nonneg hpj.le (classSpeed_pos I κ).le) (h8 κ j)
      _ = pbar I x j := rfl
  set SB := ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), x κ j
  set SG := ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B), x κ j
  have hSB : SB ≤ 1 / 2 := by nlinarith
  have hSG : 1 / 2 ≤ SG := by linarith [h1 j]
  have hck := c_pos I (k j)
  have hq : 0 ≤ I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))) :=
    mul_nonneg hpj.le (by positivity)
  calc I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)))
      ≤ 2 * (SG * (I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))))) := by
        nlinarith
    _ = 2 * ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B),
          x κ j * (I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)))) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B),
          (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        apply Finset.sum_le_sum
        intro κ hκ
        have hnot : κ ∉ badSet I x 2 j := (Finset.mem_filter.mp hκ).2
        have hle := (hk j).2 κ hnot
        have hcκ := c_pos I κ
        have hle' : (classCount I κ : ℝ) * classSpeed I κ ≤
            (classCount I (k j) : ℝ) * classSpeed I (k j) := by
          rw [mul_comm (classCount I κ : ℝ), mul_comm (classCount I (k j) : ℝ)]; exact hle
        have hinv : 1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)) ≤
            1 / ((classCount I κ : ℝ) * classSpeed I κ) :=
          one_div_le_one_div_of_le hcκ hle'
        have hx := h8 κ j
        have : 0 ≤ I.p j * x κ j := mul_nonneg hpj.le hx
        nlinarith
    _ ≤ 2 * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro κ _ _
        exact mul_nonneg (by have := c_pos I κ; positivity) (mul_nonneg hpj.le (h8 κ j))

end UniformPrecSched.Makespan.L32Aux

open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x 2 k) :
    ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * xhat I k κ j ≤
      2 * (numSpeeds I : ℝ) * D := by
  have hL : ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * xhat I k κ j =
      ∑ j, I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp [xhat, mul_comm]
  rw [hL]
  have h2 := hLP.2.1
  calc ∑ j, I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)))
      ≤ ∑ j, 2 * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) :=
        Finset.sum_le_sum (fun j _ => UniformPrecSched.Makespan.L32Aux.key I x C D hLP k hk j)
    _ = 2 * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * x κ j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ 2 * ∑ _κ : Fin (numSpeeds I), D := by
        gcongr with κ
        exact h2 κ
    _ = 2 * (numSpeeds I : ℝ) * D := by
        simp [Finset.sum_const, Finset.card_univ]; ring
