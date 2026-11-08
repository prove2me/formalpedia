-- Prove2me | solution 1 for ShapleyNV.lemma_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:11:33.81461+00:00
-- url     : https://prove2.me/submissions/63a0c39e-b356-46b6-8b61-7ad4972ec643

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

open ShapleyNV in
theorem solution {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∀ x, Finset.univ.inf' D.univ_nonempty y ≤ shapley D y x ∧
      shapley D y x ≤ Finset.univ.sup' D.univ_nonempty y := by
  intro x
  let j0 : Fin D.K := ⟨0, D.K_pos⟩
  have hM : ∀ k, y k ≤ Finset.univ.sup' D.univ_nonempty y :=
    fun k => Finset.le_sup' y (Finset.mem_univ k)
  have hM0 : 0 ≤ Finset.univ.sup' D.univ_nonempty y := le_trans (hy j0) (hM j0)
  constructor
  · unfold shapley
    apply Finset.le_inf'
    intro j _
    calc Finset.univ.inf' D.univ_nonempty y ≤ y j := Finset.inf'_le _ (Finset.mem_univ j)
      _ = shapleyA D y j j x := by unfold shapleyA; rw [if_pos rfl]
      _ ≤ Finset.univ.sup' D.univ_nonempty (fun k => shapleyA D y j k x) :=
          Finset.le_sup' (fun k => shapleyA D y j k x) (Finset.mem_univ j)
  · unfold shapley
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ j0)) ?_
    apply Finset.sup'_le
    intro k _
    unfold shapleyA
    split_ifs with h
    · exact hM k
    · have hS : 0 ≤ dist x (D.xhat j0) + dist x (D.xhat k) :=
        add_nonneg dist_nonneg dist_nonneg
      have w1 : 0 ≤ dist x (D.xhat k) / (dist x (D.xhat j0) + dist x (D.xhat k)) :=
        div_nonneg dist_nonneg hS
      have w2 : 0 ≤ dist x (D.xhat j0) / (dist x (D.xhat j0) + dist x (D.xhat k)) :=
        div_nonneg dist_nonneg hS
      have hsum : dist x (D.xhat k) / (dist x (D.xhat j0) + dist x (D.xhat k)) +
          dist x (D.xhat j0) / (dist x (D.xhat j0) + dist x (D.xhat k)) ≤ 1 := by
        rw [← add_div]
        exact div_le_one_of_le₀ (le_of_eq (add_comm _ _)) hS
      nlinarith [mul_le_mul_of_nonneg_left (hM j0) w1, mul_le_mul_of_nonneg_left (hM k) w2,
        mul_le_mul_of_nonneg_right hsum hM0]
