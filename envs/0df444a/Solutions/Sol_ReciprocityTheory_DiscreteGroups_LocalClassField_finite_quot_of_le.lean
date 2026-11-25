-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finite_quot_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:31.157135+00:00
-- url     : https://prove2.me/submissions/cf434320-1385-4e66-9e01-49bd8bd3200f

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteIndex_subG
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti


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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h' : L ≤ L') : Finite (GK p K ⧸ subG p K L) := by
  have h1 := finiteIndex_subG (p := p) (K := K) hL'
  have h2 : (subG p K L).FiniteIndex := Subgroup.finiteIndex_of_le (subG_anti h')
  exact Subgroup.finite_quotient_of_finiteIndex
end ReciprocityTheory.DiscreteGroups.LocalClassField
