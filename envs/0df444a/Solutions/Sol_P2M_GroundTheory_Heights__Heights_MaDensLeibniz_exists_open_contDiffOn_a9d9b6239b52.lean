-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:42.595827+00:00
-- url     : https://prove2.me/submissions/db363634-391a-42c4-b2c3-778202b78ebf

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLeibniz
theorem _root_.solution (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by
  obtain ⟨U, hP, hU, hzU⟩ :=
    eventually_nhds_iff.mp ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  exact ⟨U, hU, hzU, fun y hy => (hP y hy).1.contDiffWithinAt,
    fun y hy => (hP y hy).2.contDiffWithinAt⟩
end GroundTheory.Heights₂.Heights.MaDensLeibniz
