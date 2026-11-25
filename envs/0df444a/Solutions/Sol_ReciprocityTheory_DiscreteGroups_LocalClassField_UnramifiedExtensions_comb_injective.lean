-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.comb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:21:12.75596+00:00
-- url     : https://prove2.me/submissions/6f57ec3c-e4d7-42db-af9c-57ebea8b8caa

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_le_norm_sum

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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p} {K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) :
    Function.Injective (comb hKL ω hL) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  have h1 := norm_le_norm_sum p K ω hω a i
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) = 0 := congrArg Subtype.val ha
  rw [h2, norm_zero] at h1
  exact Subtype.ext (norm_le_zero_iff.1 h1)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
