-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_le_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:37.754582+00:00
-- url     : https://prove2.me/submissions/543c8313-f2a9-4ee7-a1d5-b9ecc0754832

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sum_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff


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
theorem _root_.solution {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (a : ι → K) (i : ι) :
    ‖(a i : PadicAlgCl p)‖ ≤ ‖∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖) ⟨i, Finset.mem_univ i⟩
  refine (hm i (Finset.mem_univ i)).trans ?_
  by_cases h0 : (a m : PadicAlgCl p) = 0
  · rw [h0, norm_zero]; exact norm_nonneg _
  have hpos : 0 < ‖(a m : PadicAlgCl p)‖ := norm_pos_iff.2 h0
  have hle : ∀ j, ‖(a j : PadicAlgCl p) / (a m : PadicAlgCl p)‖ ≤ 1 := by
    intro j
    rw [norm_div, div_le_one hpos]
    exact hm j (Finset.mem_univ j)
  let b : ι → Obar p := fun j => ⟨(a j : PadicAlgCl p) / (a m : PadicAlgCl p), mem_Obar_iff.2 (hle j)⟩
  have h1 := UnramifiedExtensions.norm_sum_eq_one (K := K) ω hω b (fun j => K.div_mem (a j).2 (a m).2) m
    (Subtype.ext (div_self h0))
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)
      = (a m : PadicAlgCl p) * ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = (a m : PadicAlgCl p) * ((a j : PadicAlgCl p) / (a m : PadicAlgCl p) * (ω j : PadicAlgCl p))
    field_simp
  rw [h2, norm_mul, h1, mul_one]
end ReciprocityTheory.DiscreteGroups.LocalClassField
