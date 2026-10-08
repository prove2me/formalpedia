-- Prove2me | solution 1 for TaoAnDCA.Restart.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:28:57.249325+00:00
-- url     : https://prove2.me/submissions/6719f400-4d6b-46c4-b647-4401363819ac

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem lemma_4_2 {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (mu : ℝ) (y : EuclideanSpace ℝ (Fin n)) (hy : A y + mu • y = -b) :
    ∀ x : EuclideanSpace ℝ (Fin n), TaoAnDCA.TRS.quad A b x = TaoAnDCA.TRS.quad A b y - mu / 2 * (‖x‖ ^ 2 - ‖y‖ ^ 2)
      + 1 / 2 * inner ℝ (x - y) (A (x - y) + mu • (x - y)) := by
  intro x
  have hb : b = -(A y + mu • y) := by rw [hy]; simp
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) x y
  simp only [TaoAnDCA.TRS.quad, hb, map_sub, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hcross : inner ℝ y (A x) = inner ℝ (A y) x := by
    calc
      _ = inner ℝ (A x) y := real_inner_comm _ _
      _ = inner ℝ x (A y) := hs
      _ = inner ℝ (A y) x := real_inner_comm _ _
  rw [hcross]
  simp only [real_inner_comm y x, real_inner_comm (A y) x, real_inner_comm (A y) y]
  ring

end TaoAnDCA.Restart

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (mu : ℝ) (y : EuclideanSpace ℝ (Fin n)) (hy : A y + mu • y = -b) :
    ∀ x : EuclideanSpace ℝ (Fin n), TaoAnDCA.TRS.quad A b x = TaoAnDCA.TRS.quad A b y - mu / 2 * (‖x‖ ^ 2 - ‖y‖ ^ 2)
      + 1 / 2 * inner ℝ (x - y) (A (x - y) + mu • (x - y)) := by
  intro x
  have hb : b = -(A y + mu • y) := by rw [hy]; simp
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) x y
  simp only [TaoAnDCA.TRS.quad, hb, map_sub, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hcross : inner ℝ y (A x) = inner ℝ (A y) x := by
    calc
      _ = inner ℝ (A x) y := real_inner_comm _ _
      _ = inner ℝ x (A y) := hs
      _ = inner ℝ (A y) x := real_inner_comm _ _
  rw [hcross]
  simp only [real_inner_comm y x, real_inner_comm (A y) x, real_inner_comm (A y) y]
  ring

#print axioms solution
