-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hDens_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:38.198079+00:00
-- url     : https://prove2.me/submissions/37c4d64f-d269-44cb-96ef-35308ac67665

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_contDiffOn_zero_off
import Theorems.Thm_ReciprocityTheory_AnForm_A_minorDens_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) :
    ContDiff ℝ 3 (hDens i v φ) ∧ HasCompactSupport (hDens i v φ) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  refine ⟨contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport v) hvU
    (hv.contDiffOn.mul (minorDens_contDiffOn i hU hφ 3)) fun z hz => ?_, hvc.mul_right⟩
  simp [hDens, image_eq_zero_of_notMem_tsupport hz]
end ReciprocityTheory.AnForm.A
