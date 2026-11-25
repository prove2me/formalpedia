-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.natDegree_minpoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:18.229026+00:00
-- url     : https://prove2.me/submissions/c384fd0a-18f8-4cab-b1cb-ad34344e0c2d

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_pow_of_GK


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K ^ n - 1) = 1) : (minpoly K ζ).natDegree ≤ n := by
  classical
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hsep : (minpoly K ζ).Separable := (minpoly.irreducible hint).separable
  have hcard := card_rootSet_eq_natDegree (K := PadicAlgCl p) hsep (IsAlgClosed.splits _)
  calc (minpoly K ζ).natDegree = Fintype.card ((minpoly K ζ).rootSet (PadicAlgCl p)) := hcard.symm
    _ = ((minpoly K ζ).rootSet (PadicAlgCl p)).toFinset.card := (Set.toFinset_card _).symm
    _ ≤ ((Finset.range n).image (fun i => ζ ^ (qK p K ^ i))).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Set.mem_toFinset] at hy
        obtain ⟨σ, hσ⟩ := ((isConjRoot_iff_mem_minpoly_rootSet hint).2 hy).symm.exists_algEquiv
        obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, by rw [← h, hσ]⟩
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n
end ReciprocityTheory.DiscreteGroups.LocalClassField
