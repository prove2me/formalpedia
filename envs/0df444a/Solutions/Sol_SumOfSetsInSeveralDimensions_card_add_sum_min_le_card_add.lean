-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:33.172344+00:00
-- url     : https://prove2.me/submissions/851fae7d-391e-4254-b6c3-3bfdd945a4cb

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
public import Theorems.Thm_SumOfSetsInSeveralDimensions_geometric_deletion_cases
public import Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_add_card
public import Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_add_dim
public import Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_card
public import Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_pos_of_ne_zero
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_equal_right_case
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_full_case
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_large_case
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_small_case
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_strict_right_case
public import Theorems.Thm_SumOfSetsInSeveralDimensions_zero_mem_normalize
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
private lemma sumsetCardLowerBound_le_card_add_of_zero_mem {D d : ℕ} {X Y : Finset (Fin D → ℝ)}
    (ih : ∀ {e m n : ℕ} {X' Y' : Finset (Fin D → ℝ)}, #X' = m → #Y' = n →
      m + n < #X + #Y → 1 ≤ m → m ≤ n → (X' + Y').affineDim = e →
      sumsetCardLowerBound e m n ≤ #(X' + Y'))
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) (hX : 2 ≤ #X) (hXY : #X ≤ #Y)
    (hdim : (X + Y).affineDim = d) :
    sumsetCardLowerBound d #X #Y ≤ #(X + Y) := by
  obtain ⟨hd, hcard⟩ | ⟨hd, hcard⟩ | ⟨hd, hcard⟩ | ⟨hd, hcard⟩ :=
    geometric_deletion_cases h0X h0Y hposX hposY hX (hX.trans hXY) hdim
  · refine sumsetCardLowerBound_of_full_case hX ?_ hcard
    exact ih (card_erase_of_mem h0X) (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_large_case hX hXY ?_ hcard
    exact ih (card_erase_of_mem h0X) (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_small_case hX hXY ?_ hcard
    exact ih (card_erase_of_mem h0X) rfl (by grind) (by grind) (by grind) hd
  obtain hXY | hXY := hXY.eq_or_lt
  · rw [add_comm X (Y.erase 0)] at hd hcard
    rw [← hXY]
    refine sumsetCardLowerBound_of_equal_right_case hX ?_ hcard
    exact ih (by grind [card_erase_of_mem h0Y]) rfl (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_strict_right_case (by grind) hXY ?_ hcard
    exact ih rfl (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd
private lemma sumsetCardLowerBound_le_card_add {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : (A + B).affineDim = d) :
    sumsetCardLowerBound d #B #A ≤ #(A + B) := by
  generalize hn : #A + #B = n
  induction n using Nat.strong_induction_on generalizing d A B with
  | _ n ih =>
  obtain hB1 | hB2 : #B = 1 ∨ 2 ≤ #B := by grind [hB.card_pos]
  · rw [sumsetCardLowerBound_eq, hB1]
    simpa using card_le_card_add_right hB
  have hA : A.Nonempty := card_pos.1 (by grind)
  rw [← normalize_add_card hA hB, ← normalize_card hB, ← normalize_card hA, add_comm]
  refine sumsetCardLowerBound_le_card_add_of_zero_mem ?_ (zero_mem_normalize hB)
    (zero_mem_normalize hA) (fun x hx hx0 ↦ normalize_pos_of_ne_zero hB hx hx0)
    (fun y hy hy0 ↦ normalize_pos_of_ne_zero hA hy hy0) (by simpa [normalize_card] using hB2)
    (by simpa [normalize_card] using hBA) (by rwa [add_comm, normalize_add_dim])
  rintro e m k X Y rfl rfl hlt hm hmk hdim'
  rw [add_comm X] at hdim' ⊢
  exact ih _ (by grind [normalize_card hA, normalize_card hB]) (card_pos.1 hm) hmk hdim' rfl
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : (A + B).affineDim = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  rw [← sumsetCardLowerBound_eq]
  exact sumsetCardLowerBound_le_card_add hB hBA hdim
end SumOfSetsInSeveralDimensions
