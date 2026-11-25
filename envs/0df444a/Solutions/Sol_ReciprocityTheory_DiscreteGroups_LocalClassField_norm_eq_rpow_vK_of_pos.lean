-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_eq_rpow_vK_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:09.122856+00:00
-- url     : https://prove2.me/submissions/17a2122e-2123-4845-8b0a-d75be58fa99c

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) := by
  have he' : (eK p K : ℝ) ≠ 0 := by positivity
  have h1 : - (vK p K x : ℝ) / eK p K = Real.logb p ‖((x : K) : PadicAlgCl p)‖ := by
    rw [vK_spec]; field_simp
  rw [h1, Real.rpow_logb (by linarith [one_lt_p_real p]) (one_lt_p_real p).ne' (norm_units_pos x)]
end ReciprocityTheory.DiscreteGroups.LocalClassField
