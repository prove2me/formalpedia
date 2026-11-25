-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_indicator_2f440d11df00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:15.667113+00:00
-- url     : https://prove2.me/submissions/34a852a8-e464-4943-87f8-c3a0d19ab2d6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution (A : FinHolAtlas e X) {C : Set X} (hC : IsClopen C) {u : X → ℝ}
    (hu : A.Smooth u) : A.Smooth (C.indicator u) := by
  intro j t ht
  have hto : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 t := by
    simpa using (A.chart j).open_target.mem_nhds ht.1
  by_cases htC : (A.chart j).symm t ∈ C
  · refine (((hu j).contDiffAt hto).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.isOpen htC] with t' ht'
    simp [Set.indicator_of_mem ht']
  · refine ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.compl.isOpen htC] with t' ht'
    simp [Set.indicator_of_notMem ht']
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
