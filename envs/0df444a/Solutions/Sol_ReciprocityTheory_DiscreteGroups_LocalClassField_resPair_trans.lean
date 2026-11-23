-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.resPair_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:44.325989+00:00
-- url     : https://prove2.me/submissions/6d66d36c-1732-4a00-acd7-dde350531869

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind


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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') (n : ℕ)
    (x : (kbarT p K).H n) :
    (resPair (h.trans h')).hom.H n x = (resPair h').hom.H n ((resPair h).hom.H n x) := by
  induction x using Cx.H_ind with
  | h x hx => rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
