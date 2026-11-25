-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotentialAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:59.762819+00:00
-- url     : https://prove2.me/submissions/5f1f141a-8a85-4e8c-aa68-d4f40b70900b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_add_U
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_add___822b92b3e7e3
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPotentialAddStatement := by
  intro e X _ A P Q hP hQ
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [add_U, add_φ]
    exact fun j => ((hP.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add
      ((hQ.1 x j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rw [add_U, add_U] at hy
    obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W₁, hW₁, hyW₁, G₁, hG₁, hGe₁⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W₂, hW₂, hyW₂, G₂, hG₂, hGe₂⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hyW₁, hyW₂⟩, fun z => G₁ z + G₂ z, holoOn_add A hG₁ hG₂,
      fun z hz => ?_⟩
    rw [add_U, add_U] at hz
    obtain ⟨⟨⟨hz₁, hz₂⟩, hzP, hzQ⟩, hzP', hzQ'⟩ := hz
    have e₁ := hGe₁ z ⟨⟨hz₁, hzP⟩, hzP'⟩
    have e₂ := hGe₂ z ⟨⟨hz₂, hzQ⟩, hzQ'⟩
    simp only [add_φ, Complex.add_re]
    linarith
end ReciprocityTheory.AnForm.M
