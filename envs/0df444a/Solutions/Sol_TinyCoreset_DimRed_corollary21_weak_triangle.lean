-- Prove2me | solution 1 for TinyCoreset.DimRed.corollary21_weak_triangle
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:17:18.520267+00:00
-- url     : https://prove2.me/submissions/0f1837b4-1f8c-477a-a5f1-d0c43076c152

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting
set_option autoImplicit false
open scoped Matrix
open TinyCoreset.DimRed

lemma tcd_row_ineq (D E δ ε : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (h1 : D ≤ E + δ) (h2 : E ≤ D + δ) :
    |D ^ 2 - E ^ 2| ≤ ε * D ^ 2 + (1 + 1 / ε) * δ ^ 2 := by
  have hamgm : 2 * D * δ ≤ ε * D ^ 2 + (1 / ε) * δ ^ 2 := by
    have : 0 ≤ ε * (D - δ / ε) ^ 2 := by positivity
    have e : ε * (D - δ / ε) ^ 2 = ε * D ^ 2 - 2 * D * δ + (1 / ε) * δ ^ 2 := by
      field_simp
      ring
    linarith
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  rw [abs_le]
  constructor
  · -- D² - E² ≥ -(...)
    nlinarith [mul_nonneg hD hδ, mul_nonneg hE hδ, sq_nonneg (E - D)]
  · by_cases h : δ ≤ D
    · nlinarith [mul_nonneg hD hδ, sq_nonneg (D - δ), mul_nonneg hE hδ]
    · push Not at h
      nlinarith [mul_nonneg hD hδ, sq_nonneg D, sq_nonneg E]

theorem solution {n d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (A B : Matrix (Fin n) (Fin d) ℝ)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) :
    |distSq A C - distSq B C| ≤ ε * distSq A C + (1 + 1 / ε) * frobSq (A - B) := by
  have hrow : ∀ i, |Metric.infDist (row A i) C ^ 2 - Metric.infDist (row B i) C ^ 2| ≤
      ε * Metric.infDist (row A i) C ^ 2 + (1 + 1 / ε) * (dist (row A i) (row B i)) ^ 2 := by
    intro i
    apply tcd_row_ineq _ _ _ ε Metric.infDist_nonneg Metric.infDist_nonneg dist_nonneg hε
    · exact Metric.infDist_le_infDist_add_dist
    · have : Metric.infDist (row B i) C ≤ Metric.infDist (row A i) C + dist (row B i) (row A i) :=
        Metric.infDist_le_infDist_add_dist
      rwa [dist_comm (row B i)] at this
  have hfrob : frobSq (A - B) = ∑ i, (dist (row A i) (row B i)) ^ 2 := by
    unfold frobSq
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [row, Real.dist_eq, sq_abs]
  unfold distSq
  rw [hfrob, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hrow i))
