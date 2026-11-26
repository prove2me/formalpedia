-- Prove2me | solution 1 for PsiTildeUniformBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:46.024372+00:00
-- url     : https://prove2.me/submissions/e9e7a0e5-79d9-4dd7-8805-d05a46f843d0

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiTildeUniformBound

set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psiTilde m Q ε C γ ∧
      psiTilde m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by
-- BODY
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgl : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hcoef : (0:ℝ) ≤ C * γ.len / (m : ℝ) := by positivity
  have htail : (0:ℝ) ≤ 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by positivity
  have hsumnn : (0:ℝ) ≤ ∑ i ∈ Finset.Icc 1 m,
      min (2 * C)
        (ε + 2 * C * Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)) := by
    refine Finset.sum_nonneg ?_
    intro i _
    refine le_min (by positivity) ?_
    have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    nlinarith
  unfold psiTilde
  refine ⟨add_nonneg htail (mul_nonneg hcoef hsumnn), ?_⟩
  have hsum := Finset.sum_le_sum (f := fun i : ℕ =>
      min (2 * C)
        (ε + 2 * C * Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)))
    (g := fun _ : ℕ => 2 * C) (s := Finset.Icc 1 m) (fun i _ => min_le_left _ _)
  rw [Finset.sum_const, Nat.card_Icc] at hsum
  simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hsum
  have hNc : C * γ.len / (m : ℝ) * ((m : ℝ) * (2 * C)) = 2 * C ^ 2 * γ.len := by field_simp
  have key := mul_le_mul_of_nonneg_left hsum hcoef
  rw [hNc] at key
  linarith
