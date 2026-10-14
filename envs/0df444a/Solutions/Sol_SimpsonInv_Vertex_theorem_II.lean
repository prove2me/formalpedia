-- Prove2me | solution 1 for SimpsonInv.Vertex.theorem_II
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:49:31.041986+00:00
-- url     : https://prove2.me/submissions/78854c55-93b6-4f88-a886-5842e18aaebc

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting



namespace SimpsonInv.Vertex

lemma sv_succAbove_val {m : ℕ} (j : Fin (m + 1)) (k : Fin m) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  by_cases h : k.val < j.val
  · have : k.castSucc < j := h
    rw [Fin.succAbove_of_castSucc_lt _ _ this]; simp [h]
  · have : j ≤ k.castSucc := by simpa [Fin.le_def] using h
    rw [Fin.succAbove_of_le_castSucc _ _ this]; simp [h]

lemma sv_ext_remove {m : ℕ} (S0 Sn : ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (i : ℕ) :
    extVec S0 Sn (Fin.removeNth j S) i =
      if i < j.val + 1 then extVec S0 Sn S i else extVec S0 Sn S (i + 1) := by
  have hj := j.isLt
  by_cases h0 : i = 0
  · subst h0; simp [extVec]
  by_cases hm : i ≤ m
  · have e1 : extVec S0 Sn (Fin.removeNth j S) i = S (j.succAbove ⟨i - 1, by omega⟩) := by
      simp [extVec, h0, hm, Fin.removeNth]
    rw [e1]
    by_cases hlt : i < j.val + 1
    · rw [if_pos hlt]
      have : j.succAbove ⟨i - 1, by omega⟩ = ⟨i - 1, by omega⟩ := by
        apply Fin.ext; rw [sv_succAbove_val]; dsimp only; rw [if_pos (by omega)]
      rw [this]; simp [extVec, h0, show i ≤ m + 1 by omega]
    · rw [if_neg hlt]
      have : j.succAbove ⟨i - 1, by omega⟩ = ⟨i, by omega⟩ := by
        apply Fin.ext; rw [sv_succAbove_val]; dsimp only; rw [if_neg (by omega)]; omega
      rw [this]
      have : i + 1 ≠ 0 := by omega
      simp only [extVec, this, dite_false, show i + 1 ≤ m + 1 by omega, dite_true]
      congr 1
  · have e1 : extVec S0 Sn (Fin.removeNth j S) i = Sn := by simp [extVec, h0, hm]
    rw [e1, if_neg (by omega)]
    simp [extVec, show i + 1 ≠ 0 by omega, show ¬ (i + 1 ≤ m + 1) by omega]

lemma sv_rad_remove {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (i : ℕ)
    (hi : 1 ≤ i) :
    radicand (coupledT T (j.val + 1)) S0 Sn (Fin.removeNth j S) i =
      if i < j.val + 1 then radicand T S0 Sn S i
      else if i = j.val + 1 then radicand T S0 Sn S i + radicand T S0 Sn S (i + 1)
      else radicand T S0 Sn S (i + 1) := by
  unfold radicand coupledT
  rw [sv_ext_remove, sv_ext_remove]
  by_cases h1 : i < j.val + 1
  · have : i - 1 < j.val + 1 := by omega
    simp [h1, this]
  · by_cases h2 : i = j.val + 1
    · subst h2
      have : ¬ (j.val + 1 - 1 + 1 < j.val + 1) := by omega
      have h3 : j.val + 1 - 1 < j.val + 1 := by omega
      simp only [h3, if_true, lt_irrefl, if_false, this, if_true]
      simp only [Nat.add_sub_cancel]
      ring_nf
    · have h3 : ¬ (i - 1 < j.val + 1) ↔ ¬ (i ≤ j.val + 1) := by omega
      have h4 : i - 1 + 1 = i := by omega
      have h5 : ¬ i - 1 < j.val + 1 ∨ True := Or.inr trivial
      by_cases h6 : i - 1 < j.val + 1
      · have : i = j.val + 1 + 0 := by omega
        omega
      · simp [h1, h2, h6, h4]

lemma sv_sum_shift (F : ℕ → ℝ) (p : ℕ) (hp : 1 ≤ p) (hF : F p = 0) :
    ∀ n, p ≤ n + 1 → ∑ k ∈ Finset.Icc 1 (n + 1), F k =
      ∑ i ∈ Finset.Icc 1 n, (if i < p then F i else F (i + 1)) := by
  intro n
  induction n with
  | zero => intro h; have : p = 1 := by omega
            subst this; simp [hF]
  | succ n ih =>
    intro h
    rw [Finset.sum_Icc_succ_top (a := 1) (b := n + 1) (by omega),
      Finset.sum_Icc_succ_top (a := 1) (b := n) (f := fun i => if i < p then F i else F (i + 1)) (by omega)]
    by_cases hp' : p ≤ n + 1
    · rw [ih hp']
      simp only [if_neg (show ¬ (n + 1 < p) by omega)]
    · have hp2 : p = n + 2 := by omega
      have e : F (n + 1 + 1) = 0 := by rw [← hF]; congr 1; omega
      have e2 : ∑ k ∈ Finset.Icc 1 (n + 1), F k = ∑ i ∈ Finset.Icc 1 n, (if i < p then F i else F (i + 1)) + F (n + 1) := by
        rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos (by simp at hi; omega)]
      rw [e2, e]
      simp only [if_pos (show n + 1 < p by omega)]
      ring

theorem theorem_II_core {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (hj : S j = extVec S0 Sn S j.val + T (j.val + 1)) :
    cost c r T S0 Sn S =
      cost c (coupledR r (j.val + 1)) (coupledT T (j.val + 1)) S0 Sn (Fin.removeNth j S) := by
  have hj' := j.isLt
  unfold cost
  congr 1
  have hrad0 : radicand T S0 Sn S (j.val + 1) = 0 := by
    unfold radicand
    have : extVec S0 Sn S (j.val + 1) = S j := by simp [extVec]; intro h; omega
    simp only [Nat.add_sub_cancel, this]; linarith
  set F : ℕ → ℝ := fun k => r k * Real.sqrt (radicand T S0 Sn S k) with hF
  have hFp : F (j.val + 1) = 0 := by simp [hF, hrad0]
  have h1 := sv_sum_shift F (j.val + 1) (by omega) hFp (m + 1) (by omega)
  show ∑ i ∈ Finset.Icc 1 (m + 1 + 1), F i = _
  rw [h1]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  rw [sv_rad_remove T S0 Sn S j i hi1]
  unfold coupledR
  by_cases h1 : i < j.val + 1
  · simp [h1, hF]
  · by_cases h2 : i = j.val + 1
    · subst h2
      simp only [lt_irrefl, if_false, if_true, hF, hrad0, zero_add]
    · simp [h1, h2, hF]

end SimpsonInv.Vertex

open SimpsonInv.Vertex


theorem solution {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (hj : S j = extVec S0 Sn S j.val + T (j.val + 1)) :
    cost c r T S0 Sn S =
      cost c (coupledR r (j.val + 1)) (coupledT T (j.val + 1)) S0 Sn (Fin.removeNth j S) := by
  exact theorem_II_core c S0 Sn r T S j hj
