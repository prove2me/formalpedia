-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:34:55.536876+00:00
-- url     : https://prove2.me/submissions/db2b10a9-a171-4869-976b-73ec811c5bb9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_norm_eq_of_qK
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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : ∃ y ∈ K, ‖x‖ = ‖y‖ :=
  exists_norm_eq_of_qK p K hK (le_Kn p K n) hn (finrank_Kn p K hK hn) (qK_Kn p K hK hn) hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
