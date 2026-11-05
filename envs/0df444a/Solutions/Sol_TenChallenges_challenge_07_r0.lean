-- Prove2me | solution 1 for TenChallenges.challenge_07_r0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:21.896364+00:00
-- url     : https://prove2.me/submissions/c7f32b3f-963a-4b08-aec0-2ca54f695add

import Definitions.Def_TenChallenges_Challenge_07
import Mathlib.Order.LiminfLimsup

open MeasureTheory Metric Filter
open scoped ENNReal

theorem upperDensity_mono {d : ℕ} {C D : PointSet d} (h : C ⊆ D) :
    upperDensity C ≤ upperDensity D := by
  refine limsup_le_limsup ?_
  filter_upwards [] with R
  apply ENNReal.div_le_div_right
  apply measure_mono
  intro z hz
  refine ⟨?_, hz.2⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz.1
  exact Set.mem_iUnion₂.mpr ⟨x, h hx, hzx⟩

theorem lattice_le_sphere (d : ℕ) : latticePackingConstant d ≤ spherePackingConstant d := by
  apply iSup_le
  intro L
  apply iSup_le
  intro hL
  apply iSup_le
  intro _
  exact le_iSup_of_le (L : PointSet d) (le_iSup_of_le hL le_rfl)

/-- Lattice and unrestricted packings coincide in dimension zero. -/
theorem solution : TenChallenges.statement_07 0 := by
  apply le_antisymm
  · apply iSup_le
    intro C
    apply iSup_le
    intro _
    have hpack : IsUnitPacking (Set.univ : PointSet 0) := by
      intro x _ y _ hne
      exact (hne (Subsingleton.elim x y)).elim
    have hspan : Submodule.span ℝ ((⊤ : AddSubgroup (EuclideanSpace ℝ (Fin 0))) : PointSet 0) = ⊤ := by
      simp
    exact (upperDensity_mono (Set.subset_univ C)).trans
      (le_iSup_of_le (⊤ : AddSubgroup (EuclideanSpace ℝ (Fin 0)))
        (le_iSup_of_le hpack (le_iSup_of_le hspan le_rfl)))
  · exact lattice_le_sphere 0
