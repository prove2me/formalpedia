-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isAbLK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:26.828441+00:00
-- url     : https://prove2.me/submissions/94bfef0c-7a44-482a-bb49-0b371f5808c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isAbLK_of_cyclic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_zpowers_frobLK_Kn


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
open Topology
open scoped commutatorElement
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : IsAbLK p K (Kn p K n) :=
  isAbLK_of_cyclic (finiteDimensional_Kn p K hK hn) (le_Kn p K n) (frobLK p K (Kn p K n))
    (mem_zpowers_frobLK_Kn hK hn)
end ReciprocityTheory.DiscreteGroups.LocalClassField
