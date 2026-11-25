-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:40.89962+00:00
-- url     : https://prove2.me/submissions/c8c21d55-531e-4086-af7e-6fb888cf0f29

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posDef
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_pos_of_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : LocDensPosStatement := by
  intro e X _ A Φ hΦ hpos j y hy
  have hPD : ∀ i, (hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosDef :=
    fun i => hessC_posDef _ y (potSmoothAt A (Φ i) (hΦ i) _ j ⟨hy, (Φ i).mem_U _⟩)
      (fun w hw => hpos i _ j y ⟨hy, (Φ i).mem_U _⟩ w hw)
  have hm := (ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef
    (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) hPD).2
  have hpi : 0 < (2 / Real.pi) := div_pos two_pos Real.pi_pos
  have hf : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
  exact mul_pos (mul_pos hf (pow_pos hpi e)) hm
end ReciprocityTheory.AnForm.M
