-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_lift_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:38.433744+00:00
-- url     : https://prove2.me/submissions/2e2526cd-85b5-46d9-a71e-4c22ec25a8d9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {m : ℕ} (hm : ¬ p ∣ m) {c : kbar p} (hc : c ^ m = 1) :
    ∃ ζ : PadicAlgCl p, ζ ^ m = 1 ∧ red ζ = c := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hmp : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨ζ0, hζ0⟩ := exists_primitiveRoot (p := p) hm0
  let T : Finset (kbar p) := (nthRootsFinset m (1 : PadicAlgCl p)).image red
  have hinj : Set.InjOn red (nthRootsFinset m (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
    intro x hx y hy hxy
    have hx' := (mem_nthRootsFinset hmp 1).1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    by_contra hne
    have h1 := norm_sub_eq_one_of_pow_eq_one hm hx' hy' hne
    have h2 := (red_eq_iff (norm_eq_one_of_pow hm0 hx').le (norm_eq_one_of_pow hm0 hy').le).1 hxy
    exact absurd h1 (ne_of_lt h2)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injOn hinj, hζ0.card_nthRootsFinset]
  have hsub : T ⊆ nthRootsFinset m (1 : kbar p) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    rw [mem_nthRootsFinset hmp, ← red_pow (norm_eq_one_of_pow hm0 hy').le, hy']
    have : red (1 : PadicAlgCl p) = res 1 := red_coe 1
    rw [this, map_one]
  have hle : (nthRootsFinset m (1 : kbar p)).card ≤ T.card := by
    rw [hT]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots m 1)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc' : c ∈ nthRootsFinset m (1 : kbar p) := (mem_nthRootsFinset hmp 1).2 hc
  rw [← heq] at hc'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc'
  exact ⟨y, (mem_nthRootsFinset hmp 1).1 hy, rfl⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
