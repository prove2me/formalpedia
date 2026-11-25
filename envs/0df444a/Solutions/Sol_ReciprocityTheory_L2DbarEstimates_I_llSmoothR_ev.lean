-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llSmoothR_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:11.462286+00:00
-- url     : https://prove2.me/submissions/3f285747-fa16-4051-a465-deee0ab6cfd7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llSmoothR_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have h1 : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    llSmoothR_sum n z Finset.univ (fun i x => ‖g i x‖ ^ 2)
      (fun i _ => Smooth.normSq n z (g i) (Holo.smooth n z (g i) (hg i)))
  have h2 : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  have h3 : SmoothR n z (fun _ : M => (r ^ 2)⁻¹) := Smooth.const n z (((r ^ 2)⁻¹ : ℝ) : ℂ)
  have h4 := SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) h3
  have he : ev n g ph r = fun x => (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) * (r ^ 2)⁻¹ := by
    funext x; simp [ev, div_eq_mul_inv]
  rw [he]; exact h4
end ReciprocityTheory.L2DbarEstimates.I
