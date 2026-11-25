-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_base_indep_c0ed9c553384
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:24:22.590271+00:00
-- url     : https://prove2.me/submissions/d6cbe2f7-f831-4319-a4a2-6d2e7b9bcff1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_contDiffAt_comp_symm_0d25af8a761a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_analyticAt_comp_compat_f1daebe70fc4
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
theorem _root_.solution (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {x x' p : X} (hx : p ∈ om.U x) (hx' : p ∈ om.U x')
    (hpψ : p ∈ ψ.source) (v : Fin D → ℂ) :
    levi (om.φ x ∘ ψ.symm) (ψ p) v = levi (om.φ x' ∘ ψ.symm) (ψ p) v := by
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := hpot.2 x x' p ⟨hx, hx'⟩
  obtain ⟨a, ha⟩ := A.cover p
  have hGa : AnalyticAt ℂ (G ∘ ψ.symm) (ψ p) :=
    analyticAt_comp_compat hψ ha hpψ
      (hG a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpW⟩)
  have hN : W ∩ om.U x ∩ om.U x' ∈ 𝓝 p :=
    ((hWo.inter (om.isOpen_U x)).inter (om.isOpen_U x')).mem_nhds ⟨⟨hpW, hx⟩, hx'⟩
  have hev : om.φ x ∘ ψ.symm =ᶠ[𝓝 (ψ p)]
      fun z => (om.φ x' ∘ ψ.symm) z + 1 * (G (ψ.symm z)).re := by
    filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
      (by rwa [ψ.left_inv hpψ])] with z hz
    have := hEq _ hz
    simp only [Function.comp]
    linarith
  have hre : ContDiffAt ℝ 2 (fun z => (G (ψ.symm z)).re) (ψ p) := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp (ψ p)
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun z => (G (ψ.symm z)).re) (ψ p) v = 0 := levi_re_analytic hGa v
  rw [levi_congr hev v, levi_add_smul 1
    (contDiffAt_comp_symm (om.isOpen_U x') (hpot.1 x') hψ hx' hpψ) hre v, h0]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
