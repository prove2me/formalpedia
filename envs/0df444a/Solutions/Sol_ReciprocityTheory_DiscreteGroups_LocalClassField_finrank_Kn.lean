-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:22:43.477783+00:00
-- url     : https://prove2.me/submissions/8e8d8022-f640-4669-9b0d-43f02952d165

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_extendScalars_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ_[p] (Kn p K n) = n * Module.finrank ℚ_[p] K := by
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n), finrank_extendScalars_Kn p K hK hn] at hmul
  rw [← hmul, mul_comm]
end ReciprocityTheory.DiscreteGroups.LocalClassField
