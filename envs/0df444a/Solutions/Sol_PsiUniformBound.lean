-- Prove2me | solution 1 for PsiUniformBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:13.89483+00:00
-- url     : https://prove2.me/submissions/c228149f-72a8-470d-8c24-61fc5dafed3e

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PsiUniformBound

set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psi m Q ε C γ ∧
      psi m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by
-- BODY
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgl : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hfst : (0:ℝ) ≤ 2 * C * γ.len / (m : ℝ) :=
    div_nonneg (by nlinarith) hmR.le
  have htail : (0:ℝ) ≤ 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by positivity
  unfold psi
  constructor
  · refine le_add_of_nonneg_of_le (mul_nonneg hC (Finset.sum_nonneg ?_)) htail
    intro i _
    refine le_min hfst ?_
    have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    have h2 : (0:ℝ) ≤ Metric.infDist (γ.toFun (((i : ℝ) - 1) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    nlinarith
  · have hsum := Finset.sum_le_sum (f := fun i : ℕ =>
      min (2 * C * γ.len / (m : ℝ))
        (2 * ε + 2 * C * (Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)
          + Metric.infDist (γ.toFun (((i : ℝ) - 1) * γ.len / (m : ℝ))) (Q : Set E))))
      (g := fun _ : ℕ => 2 * C * γ.len / (m : ℝ)) (s := Finset.Icc 1 m)
      (fun i _ => min_le_left _ _)
    rw [Finset.sum_const, Nat.card_Icc] at hsum
    simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hsum
    have hNc : (m : ℝ) * (2 * C * γ.len / (m : ℝ)) = 2 * C * γ.len := by field_simp
    rw [hNc] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hsum hC]
