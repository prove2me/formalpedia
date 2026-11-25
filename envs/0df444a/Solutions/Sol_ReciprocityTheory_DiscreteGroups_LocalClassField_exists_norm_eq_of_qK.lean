-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_norm_eq_of_qK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:28.081605+00:00
-- url     : https://prove2.me/submissions/799ae94e-2db1-4bf8-9d9a-f204c9fbc0af

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sum_le_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_le_norm_sum
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_comb_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_lifts
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finrank_fun
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {f : ℕ} (hf : 0 < f) (hdeg : Module.finrank ℚ_[p] L = f * Module.finrank ℚ_[p] K)
    (h : qK p L = qK p K ^ f) {x : PadicAlgCl p} (hx : x ∈ L) : ∃ y ∈ K, ‖x‖ = ‖y‖ := by
  classical
  have hL : FiniteDimensional ℚ_[p] L := by
    apply Module.finite_of_finrank_pos
    rw [hdeg]
    exact Nat.mul_pos hf Module.finrank_pos
  obtain ⟨f', hf', hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  have hff : f' = f := Nat.pow_right_injective (one_lt_qK p K hK) (hq.symm.trans h)
  subst hff
  have hsurj : Function.Surjective (UnramifiedExtensions.comb hKL ω h1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((UnramifiedExtensions.finrank_fun hK f').trans hdeg.symm)).1 (UnramifiedExtensions.comb_injective hKL ω h1 h2)
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  have hxa : x = ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) := (congrArg Subtype.val ha).symm
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖)
    ⟨⟨0, hf⟩, Finset.mem_univ _⟩
  refine ⟨a m, (a m).2, le_antisymm ?_ ?_⟩
  · rw [hxa]
    refine UnramifiedExtensions.norm_sum_le_of_le _ _ (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖(a j : PadicAlgCl p)‖ * ‖(ω j : PadicAlgCl p)‖ ≤ ‖(a j : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (UnramifiedExtensions.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖(a m : PadicAlgCl p)‖ := by rw [mul_one]; exact hm j (Finset.mem_univ j)
  · rw [hxa]
    exact norm_le_norm_sum p K ω h2 a m
end ReciprocityTheory.DiscreteGroups.LocalClassField
