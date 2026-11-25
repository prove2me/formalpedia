-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_fderiv_compat_eq_zero_1253fe46ac65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:03:00.061458+00:00
-- url     : https://prove2.me/submissions/b64e31b5-54bf-47a8-9435-e5c92c52f497

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
theorem _root_.solution {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    {a : Fin A.n} {p : X} (ha : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ}
    (h : fderiv ℂ (A.chart a ∘ ψ.symm) (ψ p) v = 0) : v = 0 := by
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have ht : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact analyticAt_compat hψ a ha hpψ
  have hid : (ψ ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm) =ᶠ[𝓝 (ψ p)] id := by
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hpψ),
      (ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
        (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds ha)] with z hz1 hz2
    simp [Function.comp, (A.chart a).left_inv hz2, ψ.right_inv hz1]
  have hD := fderiv_comp (ψ p) ht.differentiableAt hu.differentiableAt
  rw [hid.fderiv_eq, fderiv_id] at hD
  have := congrArg (fun L => L v) hD
  simpa [h] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
