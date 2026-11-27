-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_proof_8dd34c3fa381
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:00:04.522022+00:00
-- url     : https://prove2.me/submissions/a3bf38bc-bd86-416c-b796-19986c04b117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_contDiffAt_comp_symm_0d25af8a761a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_exists_levi_lower_a1c52ccadca0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
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
open ChartLeviThGe
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
namespace ChartLeviThGe
theorem _root_.solution : ChartLeviThGe.Statement := by
  intro X _ _ _ D A P om hpot hpos
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ P.mid k, ∀ x, p ∈ om.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (om.φ x ∘ (P.chart k).symm) (P.chart k p) v := by
    intro k
    obtain ⟨c, hc0, hc⟩ := exists_levi_lower hpot hpos (P.compat k) isClosed_closure.isCompact
      (P.closure_mid k)
    exact ⟨c, hc0, fun p hp => hc p (subset_closure hp)⟩
  choose c hc0 hc using hc
  have hS : 0 ≤ ∑ k, 1 / c k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (hc0 k)).le
  have hc00 : 0 < 1 / (1 + ∑ k, 1 / c k) := one_div_pos.2 (by linarith)
  have hle : ∀ k, 1 / (1 + ∑ k, 1 / c k) ≤ c k := by
    intro k
    have h1 : 1 / c k ≤ 1 + ∑ j, 1 / c j := by
      have := Finset.single_le_sum (f := fun j => 1 / c j)
        (fun j _ => (one_div_pos.2 (hc0 j)).le) (Finset.mem_univ k)
      linarith
    calc 1 / (1 + ∑ j, 1 / c j) ≤ 1 / (1 / c k) := one_div_le_one_div_of_le (one_div_pos.2 (hc0 k)) h1
      _ = c k := one_div_one_div _
  refine ⟨_, hc00, fun f a ha hf hyp => ?_⟩
  intro x k' y hy w
  set c0 := 1 / (1 + ∑ k, 1 / c k) with hc0def
  set p := (A.chart k').symm y with hpdef
  have hpA : p ∈ (A.chart k').source := (A.chart k').map_target hy.1
  have hyA : A.chart k' p = y := (A.chart k').right_inv hy.1
  obtain ⟨hpθ, hpω⟩ := hy.2
  obtain ⟨k, hk⟩ := P.cover p
  have hkm : p ∈ P.mid k := P.inner_subset_mid k hk
  have hks : p ∈ (P.chart k).source := P.mid_subset_source k hkm
  have hg : AnalyticAt ℂ (P.chart k ∘ (A.chart k').symm) y := by
    have := analyticAt_compat (P.compat k) k' hpA hks
    rwa [hyA] at this
  have hgy : (P.chart k ∘ (A.chart k').symm) y = P.chart k p := rfl

  have hω : c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 ≤
      levi (om.φ x ∘ (A.chart k').symm) y w := by
    have hev := eventuallyEq_comp_chart (om.φ x) (P.chart k) (A.chart k') hy.1 hks
    have hcd : ContDiffAt ℝ 2 (om.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart k').symm) y) :=
      contDiffAt_comp_symm (om.isOpen_U x) (hpot.1 x) (P.compat k) hpω hks
    rw [levi_congr hev w, levi_comp w hg hcd, hgy]
    exact (mul_le_mul_of_nonneg_right (hle k) (sq_nonneg _)).trans (hc k p hkm x hpω _)

  have hθ : -a * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 ≤
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart k').symm) y w := by
    obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x p ⟨hpθ, hks⟩
    have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 p :=
      ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hpθ⟩, hks⟩
    have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart k').symm =ᶠ[𝓝 y]
        fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart k').symm)) y' +
          (-1) * (G ((A.chart k').symm y')).re := by
      filter_upwards [((A.chart k').continuousAt_symm hy.1).preimage_mem_nhds hN] with y' hy'
      have h1 := hEq _ hy'
      simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
      linarith
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k').symm) y := hG k' y ⟨hy.1, hpW⟩
    have hcf : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart k').symm) y) := by
      have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k p) :=
        ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
          ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
      have hfψ := contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ p) hks
      exact hq.add hfψ
    have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart k').symm)) y :=
      hcf.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
    have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart k').symm y')).re) y := by
      have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
        ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
      simpa [Function.comp_def] using this
    have h0 : levi (fun y' => (G ((A.chart k').symm y')).re) y w = 0 := levi_re_analytic hGa w
    rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf, hgy]
    have := hyp k p hkm (fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w)
    linarith
  have hac : 0 ≤ a / c0 := div_nonneg ha hc00.le
  have h1 : -(a / c0) * levi (om.φ x ∘ (A.chart k').symm) y w ≤
      -(a / c0) * (c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2) :=
    mul_le_mul_of_nonpos_left hω (by linarith)
  have h2 : -(a / c0) * (c0 * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2) =
      -a * ‖fderiv ℂ (P.chart k ∘ (A.chart k').symm) y w‖ ^ 2 := by
    field_simp
  linarith
end ChartLeviThGe
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
