-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotentialPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:02.092536+00:00
-- url     : https://prove2.me/submissions/581334b9-6140-4ba1-9a1a-9bb45d50c184

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiffAt_of_isPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
section SlopeTestRemainingChoices
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end SlopeTestRemainingChoices
private theorem eventually_chart_symm_chart_comp_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X) (hh : Continuous h)
    (j : Fin B.n) (k : Fin A.n) {w : Fin e' → ℂ} (hw : w ∈ (B.chart j).target)
    (hk : h ((B.chart j).symm w) ∈ (A.chart k).source) :
    ∀ᶠ w' in 𝓝 w, (A.chart k).symm (A.chart k (h ((B.chart j).symm w'))) = h ((B.chart j).symm w') := by
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh)
  filter_upwards [hO.mem_nhds ⟨hw, hk⟩] with w' hw'
  exact (A.chart k).left_inv hw'.2
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPotentialPullbackStatement := by
  intro e e' X Y _ _ A B h hh P hP
  refine ⟨fun y j w hw => ?_, fun y y' z hz => ?_⟩
  · obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y) := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ P.U (h y)
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hf := contDiffAt_of_isPotential A P hP (h y) k hin
    have hg : ContDiffAt ℝ ∞ (A.chart k ∘ h ∘ (B.chart j).symm) w :=
      (AnalyticAt.contDiffAt (n := ∞) (hh.2 j k w ⟨hw.1, hk⟩)).restrict_scalars ℝ
    refine (ContDiffAt.congr_of_eventuallyEq (hf.comp w hg) ?_).contDiffWithinAt
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show P.φ (h y) (h ((B.chart j).symm w')) =
      P.φ (h y) ((A.chart k).symm (A.chart k (h ((B.chart j).symm w'))))
    rw [hw']
  · have hz' : h z ∈ P.U (h y) ∩ P.U (h y') := hz
    obtain ⟨W, hW, hzW, G, hG, hGe⟩ := hP.2 (h y) (h y') (h z) hz'
    refine ⟨h ⁻¹' W, hW.preimage hh.1, hzW, G ∘ h, fun j w hw => ?_, fun z' hz' => hGe (h z') hz'⟩
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' W := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ W
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hc : AnalyticAt ℂ ((G ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) w :=
      AnalyticAt.comp (hG k _ hin) (hh.2 j k w ⟨hw.1, hk⟩)
    refine hc.congr ?_
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show G ((A.chart k).symm (A.chart k (h ((B.chart j).symm w')))) = G (h ((B.chart j).symm w'))
    rw [hw']
end ReciprocityTheory.AnForm.M
