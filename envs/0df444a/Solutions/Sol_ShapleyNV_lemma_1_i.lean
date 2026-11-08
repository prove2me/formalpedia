-- Prove2me | solution 1 for ShapleyNV.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:06:18.177204+00:00
-- url     : https://prove2.me/submissions/258673a0-3576-431d-87ad-b8e19a193297

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

open ShapleyNV in
theorem solution {X : Type*} [MetricSpace X] (D : ShapleyNV.Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∀ k, ShapleyNV.shapley D y (D.xhat k) = y k := by
  intro k
  have hA : ∀ j, ShapleyNV.shapleyA D y j k (D.xhat k) = y k := by
    intro j
    unfold ShapleyNV.shapleyA
    by_cases h : j = k
    · rw [if_pos h]
    · rw [if_neg h]
      have hd : 0 < dist (D.xhat k) (D.xhat j) := dist_pos.2 (fun e => h (D.xhat_inj e).symm)
      simp [hd.ne']
  have hrow : ∀ k', ShapleyNV.shapleyA D y k k' (D.xhat k) = y k := by
    intro k'
    unfold ShapleyNV.shapleyA
    by_cases h : k = k'
    · rw [if_pos h, h]
    · rw [if_neg h]
      have hd : 0 < dist (D.xhat k) (D.xhat k') := dist_pos.2 (fun e => h (D.xhat_inj e))
      simp [hd.ne']
  unfold ShapleyNV.shapley
  apply le_antisymm
  · exact (Finset.inf'_le _ (Finset.mem_univ k)).trans
      (Finset.sup'_le _ _ (fun k' _ => (hrow k').le))
  · exact Finset.le_inf' _ _ (fun j _ => (hA j).symm.le.trans
      (Finset.le_sup' (fun k' => ShapleyNV.shapleyA D y j k' (D.xhat k)) (Finset.mem_univ k)))
