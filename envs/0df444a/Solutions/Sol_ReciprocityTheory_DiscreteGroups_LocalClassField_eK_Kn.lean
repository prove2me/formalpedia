-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:27.703431+00:00
-- url     : https://prove2.me/submissions/5e3bef06-9b4d-41c7-af4e-7f763647f4e0

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eK_eq_of_norm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_Kn


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
variable {K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eK p (Kn p K n) = eK p K :=
  eK_eq_of_norm p (le_Kn p K n) fun _ hx => norm_Kn p K hK hn hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
