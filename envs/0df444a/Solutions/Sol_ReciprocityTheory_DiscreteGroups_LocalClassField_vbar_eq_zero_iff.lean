-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.vbar_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:42.574403+00:00
-- url     : https://prove2.me/submissions/a262bea7-898f-47fc-86dc-7f238b09bbc9

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [(subG p K L).Normal]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (x : KbarMult p) :
    vbar p x = 0 ↔ ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : 0 < ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ :=
    norm_pos_iff.2 (Units.ne_zero _)
  rw [vbar_apply, neg_eq_zero, Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h) <;> linarith
  · intro h; right; right; right; right; left; exact h
end ReciprocityTheory.DiscreteGroups.LocalClassField
