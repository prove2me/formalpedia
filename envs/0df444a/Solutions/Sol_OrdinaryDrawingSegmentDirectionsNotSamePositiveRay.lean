-- Prove2me | solution 1 for OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:28:48.067021+00:00
-- url     : https://prove2.me/submissions/fb227728-083a-41ae-b0c6-a04d91ee1b27

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma ef1154a3_mem {x d : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    x + t • d ∈ segment ℝ x (x + d) := by
  rw [segment_eq_image']
  exact ⟨t, ⟨h0, h1⟩, by simp⟩

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    {e f : G.edgeFinset} (hef : e ≠ f)
    {i j : ℕ}
    (hi : i + 1 < (D.edgeArc e).vertices.length)
    (hj : j + 1 < (D.edgeArc f).vertices.length)
    {x d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0)
    (hseg_e :
      segment ℝ x (x + d) =
        segment ℝ (D.edgeArc e).vertices[i] (D.edgeArc e).vertices[i + 1])
    (hseg_f :
      segment ℝ x (x + v) =
        segment ℝ (D.edgeArc f).vertices[j] (D.edgeArc f).vertices[j + 1]) :
    ¬ ∃ a : ℝ, 0 < a ∧ v = a • d := by
  rintro ⟨a, ha, rfl⟩
  apply D.no_shared_nondegenerate_subarc hef
  set b : ℝ := min a 1 with hb
  have hb0 : 0 < b := lt_min ha one_pos
  refine ⟨i, j, hi, hj, x, x + b • d, ?_, ?_⟩
  · intro h
    have : b • d = 0 := by
      have := congrArg (fun y => y - x) h
      simpa using this.symm
    rcases smul_eq_zero.mp this with h' | h'
    · exact hb0.ne' h'
    · exact hd h'
  · rw [← hseg_e, ← hseg_f]
    have h1 : x + b • d ∈ segment ℝ x (x + d) :=
      ef1154a3_mem hb0.le (min_le_right _ _)
    have hx : x + b • d = x + (b / a) • (a • d) := by
      have hba : b / a * a = b := div_mul_cancel₀ b ha.ne'
      rw [smul_smul, hba]
    have h2 : x + b • d ∈ segment ℝ x (x + a • d) := by
      rw [hx]
      exact ef1154a3_mem (div_nonneg hb0.le ha.le)
        ((div_le_one ha).mpr (min_le_left _ _))
    exact Set.subset_inter
      ((convex_segment x (x + d)).segment_subset (left_mem_segment ℝ x (x + d)) h1)
      ((convex_segment x (x + a • d)).segment_subset (left_mem_segment ℝ x (x + a • d)) h2)
