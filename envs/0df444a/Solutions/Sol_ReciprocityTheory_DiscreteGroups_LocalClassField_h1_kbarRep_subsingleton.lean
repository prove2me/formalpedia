-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h1_kbarRep_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:09.206909+00:00
-- url     : https://prove2.me/submissions/970a70c2-d61c-4184-8de9-f9484f9dd19a

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbar_cocycle

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
theorem _root_.solution : Subsingleton (H1 (kbarRep p K)) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  rw [Submodule.mem_comap]
  show z ∈ Bd1 _
  rw [mem_contCoboundaries1]
  exact kbar_cocycle p K z hz.1 hz.2
end ReciprocityTheory.DiscreteGroups.LocalClassField
