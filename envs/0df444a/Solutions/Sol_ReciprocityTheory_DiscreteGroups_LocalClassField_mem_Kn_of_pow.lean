-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kn_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:50.840967+00:00
-- url     : https://prove2.me/submissions/bf98644f-ed9c-4a06-8de1-cb7109422397

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  UnramifiedExtensions.mem_Kn_of_pow K hζ
end ReciprocityTheory.DiscreteGroups.LocalClassField
