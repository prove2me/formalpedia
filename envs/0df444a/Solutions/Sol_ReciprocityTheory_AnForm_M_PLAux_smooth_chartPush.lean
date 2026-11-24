-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.smooth_chartPush
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:55.759375+00:00
-- url     : https://prove2.me/submissions/19dcded2-30d6-4941-836e-3576d5097aaf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution [T2Space X] {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {F : (Fin e → ℂ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) : A.Smooth (chartPush ψ F) := by
  intro a y hy
  refine ContDiffAt.contDiffWithinAt ?_
  set C := ψ.symm '' tsupport F
  have hC : IsClosed C := (isCompact_symm_image hK hKt).isClosed
  by_cases hs : (A.chart a).symm y ∈ ψ.source
  · have hya : (A.chart a).symm y ∈ (A.chart a).source := (A.chart a).map_target hy.1
    have h2 : ContDiffAt ℝ ∞ (ψ ∘ (A.chart a).symm) y := by
      have := (analyticAt_compat hψ a hya hs).contDiffAt (n := ∞)
      rw [(A.chart a).right_inv hy.1] at this
      exact this.restrict_scalars ℝ
    refine (hF.contDiffAt.comp y h2).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        ψ.open_source).mem_nhds ⟨hy.1, hs⟩
    filter_upwards [hN] with y' hy'
    simp only [chartPush, Function.comp_apply]
    rw [Set.indicator_of_mem (show (A.chart a).symm y' ∈ ψ.source from hy'.2)]
    rfl
  · have hnC : (A.chart a).symm y ∉ C := fun h => hs (by
      obtain ⟨z, hz, hzz⟩ := h
      rw [← hzz]; exact ψ.map_target (hKt hz))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' Cᶜ ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        hC.isOpen_compl).mem_nhds ⟨hy.1, hnC⟩
    filter_upwards [hN] with y' hy'
    exact chartPush_eq_zero ψ hy'.2
end ReciprocityTheory.AnForm.M.PLAux
