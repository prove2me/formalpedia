-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:05.698332+00:00
-- url     : https://prove2.me/submissions/9e4fb88b-9fc0-4929-ba2b-ed66bf8ca921

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (C : ℝ)
    (hC : ∀ x, ‖φ x - x‖ ≤ C) (g : (Fin n → ℝ) → ℝ) (hgc : HasCompactSupport g)
    (y₀ : Fin n → ℝ) : HasCompactSupport fun x => g (φ x - y₀) := by
  obtain ⟨r, hr⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (r + ‖y₀‖ + C))
    fun x hx => ?_
  by_contra hne
  have h1 := hr (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff] at h1
  apply hx
  rw [mem_closedBall_zero_iff]
  have h2 : ‖x‖ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by
    calc ‖x‖ = ‖(φ x - y₀) + y₀ - (φ x - x)‖ := by congr 1; abel
      _ ≤ ‖(φ x - y₀) + y₀‖ + ‖φ x - x‖ := norm_sub_le _ _
      _ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
  linarith [hC x]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
