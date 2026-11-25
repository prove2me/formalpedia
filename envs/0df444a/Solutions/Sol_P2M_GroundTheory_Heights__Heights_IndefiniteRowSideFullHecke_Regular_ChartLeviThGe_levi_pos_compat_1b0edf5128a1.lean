-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:09.235425+00:00
-- url     : https://prove2.me/submissions/efc73bc2-18c7-4a8f-8daf-24daf5861cf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_compat_chart_63c19b4cc322
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_contDiffAt_comp_symm_0d25af8a761a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_fderiv_compat_eq_zero_1253fe46ac65
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {om : LocPot X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
theorem _root_.solution (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {x p : X}
    (hpx : p ∈ om.U x) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ} (hv : v ≠ 0) :
    0 < levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  obtain ⟨a, ha⟩ := A.cover p
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have hev := eventuallyEq_comp_chart (om.φ x) (A.chart a) ψ (ψ.map_source hpψ)
    (by rwa [ψ.left_inv hpψ])
  have hcd : ContDiffAt ℝ 2 (om.φ x ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact contDiffAt_comp_symm (om.isOpen_U x) (hpot.1 x) (compat_chart A a) hpx ha
  rw [levi_congr hev v, levi_comp v hu hcd, huy]
  refine hpos x a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpx⟩ _ ?_
  intro h0
  exact hv (fderiv_compat_eq_zero hψ ha hpψ h0)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
