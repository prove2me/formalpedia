-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.rpow_neg_div_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:32.111396+00:00
-- url     : https://prove2.me/submissions/9c38c672-d2fe-439b-9a50-3de9bcf9c27b

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_p_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (he : 0 < eK p K) {i : ℕ} (hi : 0 < i) : (p : ℝ) ^ (- (i : ℝ) / eK p K) < 1 := by
  have he' : (0 : ℝ) < eK p K := by positivity
  have hi' : (0 : ℝ) < i := by positivity
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_p_real p) (div_neg_of_neg_of_pos (by linarith) he')
end ReciprocityTheory.DiscreteGroups.LocalClassField
