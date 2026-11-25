-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eK_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:27.319183+00:00
-- url     : https://prove2.me/submissions/cd0a76c9-2934-400a-8a92-cde46afc1cf4

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eK_eq_of_norm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_iff
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
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) : eK p (MaximalUnramifiedExtension p K) = eK p K :=
  eK_eq_of_norm p le_Kur fun x hx => by
    obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
    exact norm_Kn p K hK hn hxn
end ReciprocityTheory.DiscreteGroups.LocalClassField
