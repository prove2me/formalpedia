-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.isTest_logCutoff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:44.368039+00:00
-- url     : https://prove2.me/submissions/accfc714-79e9-41ee-9422-35f9bc22b6e5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_logCutoff_eventuallyEq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_contDiffAt_logCutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ}
    (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z) {k : ℝ} (hk : 0 < k) {g : V n → ℂ} (hg : IsTest Ω g) :
    IsTest (Ω \ {z | F z = 0}) (fun z => (extCut F k z : ℂ) * g z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport g
    · have hzΩ : z ∈ Ω := hg.2.2 hz
      have hc : ContDiffAt ℝ ∞ (fun w => (extCut F k w : ℂ)) z :=
        ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_logCutoff hk (hsm z hzΩ))
      exact hc.mul (hg.1.contDiffAt)
    · have hg0 : g =ᶠ[𝓝 z] 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℂ)) z).congr_of_eventuallyEq ?_
      filter_upwards [hg0] with w hw
      simp [hw]
  · exact hg.2.1.mul_left
  · intro z hz
    have hzg : z ∈ tsupport g := tsupport_mul_subset_right hz
    have hzΩ : z ∈ Ω := hg.2.2 hzg
    refine ⟨hzΩ, ?_⟩
    intro hF0
    have hF0' : F z = 0 := hF0
    have hcut := logCutoff_eventuallyEq_zero hk (hsm z hzΩ).continuousAt hF0'
    have hprod : (fun w => (extCut F k w : ℂ) * g w) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hcut] with w hw
      simp [hw]
    exact ((notMem_tsupport_iff_eventuallyEq).2 hprod) hz
end ReciprocityTheory.L2DbarEstimates.C
