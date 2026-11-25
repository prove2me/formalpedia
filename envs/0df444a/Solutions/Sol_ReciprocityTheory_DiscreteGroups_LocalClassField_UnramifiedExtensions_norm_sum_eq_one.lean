-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:06.366558+00:00
-- url     : https://prove2.me/submissions/cd3ad23a-8ca6-4755-83c0-165d555a6d74

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_resK_iff


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
variable {p}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (b : ι → Obar p)
    (hb : ∀ j, (b j : PadicAlgCl p) ∈ K) (i : ι) (hi : b i = 1) :
    ‖∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ = 1 := by
  have hs : ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) = ((∑ j, b j * ω j : Obar p) : PadicAlgCl p) := by
    push_cast; rfl
  rw [hs]
  refine le_antisymm (norm_le_one _) (not_lt.1 fun hlt => ?_)
  have h0 := (res_eq_zero_iff _).2 hlt
  rw [map_sum] at h0
  let c : ι → resK p K := fun j => ⟨res (b j), (mem_resK_iff K _).2 ⟨b j, hb j, rfl⟩⟩
  have h1 : ∑ j, c j • IsLocalRing.residue (Obar p) (ω j) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, map_mul]
  have h2 := Fintype.linearIndependent_iff.1 hω c h1 i
  have h3 : res (b i) = 0 := congrArg Subtype.val h2
  rw [hi, map_one] at h3
  exact one_ne_zero h3
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
