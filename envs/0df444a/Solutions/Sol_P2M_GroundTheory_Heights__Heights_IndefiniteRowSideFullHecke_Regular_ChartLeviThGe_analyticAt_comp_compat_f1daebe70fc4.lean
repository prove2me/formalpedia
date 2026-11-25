-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_analyticAt_comp_compat_f1daebe70fc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:14.929209+00:00
-- url     : https://prove2.me/submissions/f947d020-6a40-4601-9f5d-cece3e7e653b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {F : X → E} {a : Fin A.n}
    {p : X} (hpa : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source)
    (hF : AnalyticAt ℂ (F ∘ (A.chart a).symm) (A.chart a p)) :
    AnalyticAt ℂ (F ∘ ψ.symm) (ψ p) := by
  have h1 : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using hpa⟩
  have h2 : AnalyticAt ℂ ((F ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm)) (ψ p) :=
    hF.comp_of_eq h1 (by simp [ψ.left_inv hpψ])
  refine h2.congr ?_
  filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
    (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds hpa)] with z hz
  simp [Function.comp, (A.chart a).left_inv hz]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
