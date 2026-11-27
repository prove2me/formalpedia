-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:59.357131+00:00
-- url     : https://prove2.me/submissions/427df868-75d5-472c-8f95-4cc4363b0050

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix Filter Topology Set
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by
  intro x hx
  let e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' B) := hB.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' B) :=
    hf.comp e.symm.differentiable.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU hg (e x) (by simpa using hx)
  have hfe : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [hfe]
  exact ha.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)).analyticAt x)
end ReciprocityTheory.MultiplicativeHeights
