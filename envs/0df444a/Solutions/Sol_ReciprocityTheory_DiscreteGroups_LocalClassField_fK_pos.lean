-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.fK_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:08.202807+00:00
-- url     : https://prove2.me/submissions/3b6d0e96-694e-4a81-89a5-051fedd3adb3

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_eq_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_eq_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) : 0 < fK p K := by
  obtain ⟨f, hf0, hf⟩ := qK_eq_pow p K hK
  rwa [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]
end ReciprocityTheory.DiscreteGroups.LocalClassField
