-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.mem_resK_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:04.614837+00:00
-- url     : https://prove2.me/submissions/15d7b8f7-143d-48c2-b8bd-0017e72cac53

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_qK_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finite_resK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK


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
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {c : kbar p} (h : c ^ qK p K = c) : c ∈ resK p K := by
  classical
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hq := one_lt_qK K hK
  set P : (kbar p)[X] := X ^ qK p K - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (kbar p) hq
  have hdeg : P.natDegree = qK p K := FiniteField.X_pow_card_sub_X_natDegree_eq (kbar p) hq
  let T : Finset (kbar p) := (Finset.univ : Finset (resK p K)).image Subtype.val
  have hT : T.card = qK p K := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, qK,
      Nat.card_eq_fintype_card]
  have hsub : T ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [pow_qK_eq K hK y.2]
  have hle : P.roots.toFinset.card ≤ T.card := by
    rw [hT, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc : c ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [h]
  rw [← heq] at hc
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hc
  exact y.2
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
