-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:43.172462+00:00
-- url     : https://prove2.me/submissions/1a9fb1b2-a5ee-4d01-8612-dbf2b6ced52e

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) : qK p K = p ^ fK p K := by
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  rw [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]
end ReciprocityTheory.DiscreteGroups.LocalClassField
