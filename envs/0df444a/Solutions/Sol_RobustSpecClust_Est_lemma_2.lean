-- Prove2me | solution 1 for RobustSpecClust.Est.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:11:04.290792+00:00
-- url     : https://prove2.me/submissions/45efb259-0d94-4891-bfc6-3a3ba8d25e8e

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

open RobustSpecClust.Est in
theorem solution {n m r : ℕ} (hr : 2 ≤ r) (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r)
    (τin : ℝ) (τout : Fin r → Fin r → ℝ) (γ : ℝ) (Xh : Matrix (Pt n m) (Pt n m) ℝ)
    (hXh : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1) :
    (∀ a b : ℝ,
      (∀ i j, φ i = φ j → a ≤ refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j)) →
      (∀ i j, φ i ≠ φ j → refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) ≤ b) →
      b < γ → γ < a →
      l1 (inlierBlock Xh - inlierBlock (trueClust (m := m) φ)) ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - Xh) /
          min (a - γ) (γ - b)) ∧
    (∀ υ : ℝ, 0 < υ → υ < 1 → tauOutMax τout hr < τin →
      γ = υ * τin + (1 - υ) * tauOutMax τout hr →
      l1 (inlierBlock Xh - inlierBlock (trueClust (m := m) φ)) ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - Xh) /
          (min υ (1 - υ) * (τin - tauOutMax τout hr))) := by
  have part1 : ∀ a b : ℝ,
      (∀ i j, φ i = φ j → a ≤ refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j)) →
      (∀ i j, φ i ≠ φ j → refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) ≤ b) →
      b < γ → γ < a →
      l1 (inlierBlock Xh - inlierBlock (trueClust (m := m) φ)) ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - Xh) /
          min (a - γ) (γ - b) := by
    intro a b ha hb hbγ hγa
    have hc : 0 < min (a - γ) (γ - b) := lt_min (by linarith) (by linarith)
    rw [le_div_iff₀ hc]
    have z1 : ∀ (i : Fin n) (o : Fin m),
        (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (Sum.inl i) (Sum.inr o) = 0 := by
      intro i o; simp [refMatrix, ones]
    have z2 : ∀ (o : Fin m) (j : Fin n),
        (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (Sum.inr o) (Sum.inl j) = 0 := by
      intro o j; simp [refMatrix, ones]
    have z3 : ∀ (o o' : Fin m),
        (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (Sum.inr o) (Sum.inr o') = 0 := by
      intro o o'; simp [refMatrix, ones]
    unfold frobInner
    simp only [Fintype.sum_sum_type, z1, z2, z3, zero_mul, Finset.sum_const_zero, add_zero]
    unfold l1 inlierBlock
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨h0, h1⟩ := hXh (Sum.inl i) (Sum.inl j)
    have hmin1 := min_le_left (a - γ) (γ - b)
    have hmin2 := min_le_right (a - γ) (γ - b)
    by_cases hij : φ i = φ j
    · have hR := ha i j hij
      have hT : trueClust (m := m) φ (Sum.inl i) (Sum.inl j) = 1 := by simp [trueClust, hij]
      show |Xh (Sum.inl i) (Sum.inl j) - trueClust (m := m) φ (Sum.inl i) (Sum.inl j)| *
          min (a - γ) (γ - b) ≤ (refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) - γ * 1) *
          (trueClust (m := m) φ (Sum.inl i) (Sum.inl j) - Xh (Sum.inl i) (Sum.inl j))
      rw [hT, mul_one]
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · have hR := hb i j hij
      have hT : trueClust (m := m) φ (Sum.inl i) (Sum.inl j) = 0 := by simp [trueClust, hij]
      show |Xh (Sum.inl i) (Sum.inl j) - trueClust (m := m) φ (Sum.inl i) (Sum.inl j)| *
          min (a - γ) (γ - b) ≤ (refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) - γ * 1) *
          (trueClust (m := m) φ (Sum.inl i) (Sum.inl j) - Xh (Sum.inl i) (Sum.inl j))
      rw [hT, mul_one]
      rw [sub_zero, abs_of_nonneg h0]
      nlinarith
  refine ⟨part1, ?_⟩
  intro υ hυ0 hυ1 hlt hγ
  have hD : 0 < τin - tauOutMax τout hr := by linarith
  have key := part1 τin (tauOutMax τout hr) ?_ ?_ ?_ ?_
  · have hm : min (τin - γ) (γ - tauOutMax τout hr) = min υ (1 - υ) * (τin - tauOutMax τout hr) := by
      rw [min_mul_of_nonneg _ _ hD.le, min_comm, hγ]
      congr 1 <;> ring
    rw [hm] at key
    exact key
  · intro i j hij
    simp only [refMatrix, if_pos hij]
    exact le_max_right _ _
  · intro i j hij
    simp only [refMatrix, if_neg hij]
    have hmem : (φ i, φ j) ∈ (Finset.univ : Finset (Fin r)).offDiag := by
      simp [Finset.mem_offDiag, hij]
    have hle0 := Finset.le_sup' (s := (Finset.univ : Finset (Fin r)).offDiag)
      (fun p => τout p.1 p.2) hmem
    have hle : τout (φ i) (φ j) ≤ tauOutMax τout hr := hle0
    exact (min_le_right _ _).trans hle
  · rw [hγ]; nlinarith
  · rw [hγ]; nlinarith
