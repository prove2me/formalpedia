-- Prove2me | solution 1 for RobustCorrClust.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:00:50.76604+00:00
-- url     : https://prove2.me/submissions/8c69c17c-5bd0-4662-878e-4f900553dee6

import Mathlib
import Definitions.Def_RobustCorrClust_Main_Sparsifier

set_option autoImplicit false

open RobustCorrClust.Main

open Finset Matrix

/-- For `f` symmetric, `∑_{u,v} f u v = 2 ∑_{u<v} f u v + ∑_u f u u`. -/
private lemma sum_sym {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ u v, f u v = f v u) :
    ∑ u, ∑ v, f u v = 2 * pairSum f + ∑ u, f u u := by
  have split : ∀ u v, f u v = (if u < v then f u v else 0) + (if v < u then f v u else 0)
      + (if u = v then f u v else 0) := by
    intro u v
    rcases lt_trichotomy u v with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le, hf u v]
  have h2 : ∑ u : Fin n, ∑ v : Fin n, (if v < u then f v u else 0) = pairSum f := by
    unfold pairSum; exact Finset.sum_comm
  calc ∑ u, ∑ v, f u v
      = ∑ u : Fin n, ∑ v : Fin n, ((if u < v then f u v else 0) + (if v < u then f v u else 0)
          + (if u = v then f u v else 0)) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => split u v
    _ = 2 * pairSum f + ∑ u, f u u := by
        simp only [Finset.sum_add_distrib, h2]
        unfold pairSum
        simp [Finset.sum_ite_eq]
        ring

private lemma adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adjMat G u v = adjMat G v u := by
  unfold adjMat
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

private lemma adj_diag {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : adjMat G u u = 0 := by
  unfold adjMat; simp

private lemma adj_sq {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adjMat G u v ^ 2 = adjMat G u v := by
  unfold adjMat; split_ifs <;> norm_num

private lemma sum_adj {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∑ u, ∑ v, adjMat G u v = 2 * (numPos G : ℝ) := by
  classical
  have hrow : ∀ u, ∑ v, adjMat G u v = (G.degree u : ℝ) := by
    intro u
    unfold adjMat
    rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  simp only [hrow]
  rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  unfold numPos
  push_cast
  congr 2

private lemma pairSum_adj {n : ℕ} (G : SimpleGraph (Fin n)) :
    pairSum (adjMat G) = (numPos G : ℝ) := by
  have := sum_sym (adjMat G) (adj_symm G)
  rw [sum_adj] at this
  simp only [adj_diag, Finset.sum_const_zero, add_zero] at this
  linarith

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.IsSymm) (hdiag : ∀ u, Y u u = 1) :
    PsiG G Y = frobInner (lap (adjMat G)) Y + frobSq Y / 2 - (n : ℝ) / 2
      - (numPos G : ℝ) := by
  have hYs : ∀ u v, Y u v = Y v u := fun u v => hY.apply v u
  -- ⟨L, Y⟩ = ∑_{u,v} A - ∑_{u,v} A Y
  have hL : frobInner (lap (adjMat G)) Y = ∑ u, ∑ v, adjMat G u v - ∑ u, ∑ v, adjMat G u v * Y u v := by
    unfold frobInner lap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hdiag, mul_one]
  have hAY := sum_sym (fun u v => adjMat G u v * Y u v)
    (fun u v => by rw [adj_symm G u v, hYs u v])
  have hYY := sum_sym (fun u v => Y u v * Y u v) (fun u v => by rw [hYs u v])
  have hAA := pairSum_adj G
  have hsA := sum_adj G
  have hF : frobSq Y = ∑ u, ∑ v, Y u v * Y u v := rfl
  simp only [hdiag, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hYY
  have hAd : ∀ u, adjMat G u u = 0 := adj_diag G
  simp only [hAd, zero_mul, Finset.sum_const_zero, add_zero] at hAY
  have hPsi : PsiG G Y = pairSum (fun u v => Y u v * Y u v)
      - 2 * pairSum (fun u v => adjMat G u v * Y u v) + pairSum (adjMat G) := by
    unfold PsiG pairSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs
    · linear_combination adj_sq G u v
    · ring
  rw [hPsi, hL, hF, hYY, hAY, hsA, hAA]
  ring
