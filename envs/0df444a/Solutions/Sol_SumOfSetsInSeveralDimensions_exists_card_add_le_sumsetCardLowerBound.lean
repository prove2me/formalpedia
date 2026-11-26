-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.exists_card_add_le_sumsetCardLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:29.241816+00:00
-- url     : https://prove2.me/submissions/b53abe6a-9f55-4993-82e0-054ede388a11

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_axisPoints
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_unitVectors
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_axisUnionBasis
public import Theorems.Thm_SumOfSetsInSeveralDimensions_axisPoints_mono
public import Theorems.Thm_SumOfSetsInSeveralDimensions_unitVectors_mono
public import Theorems.Thm_SumOfSetsInSeveralDimensions_axisPoints_add_axisPoints_subset
public import Theorems.Thm_SumOfSetsInSeveralDimensions_affineDim_axisUnionBasis
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_add_le
public import Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_sumsetCardLowerBound_add_add
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
private lemma card_add_self_le {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) :
    #(S + S) ≤ (#S + 1).choose 2 := by
  rw [← card_sym2]
  refine (card_le_card ?_).trans (card_image_le (f := Sym2.lift ⟨(· + ·), add_comm⟩))
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  exact mem_image.2 ⟨s(a, b), mk_mem_sym2_iff.2 ⟨ha, hb⟩, rfl⟩
private lemma card_unitVectors_add_le {c : ℕ} (hc : c ≤ e) :
    #(unitVectors e c + unitVectors e e) ≤ (c + 1).choose 2 + c * (e - c) := by
  have hsub : unitVectors e c + unitVectors e e ⊆ (unitVectors e c + unitVectors e c) ∪
      (unitVectors e c + (unitVectors e e \ unitVectors e c)) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
    by_cases hbc : b ∈ unitVectors e c
    · exact mem_union_left _ (add_mem_add ha hbc)
    · exact mem_union_right _ (add_mem_add ha (mem_sdiff.2 ⟨hb, hbc⟩))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
  · simpa [card_unitVectors hc] using card_add_self_le (unitVectors e c)
  · refine card_add_le.trans_eq ?_
    rw [card_sdiff_of_subset (unitVectors_mono hc), card_unitVectors hc, card_unitVectors le_rfl]
private lemma axisUnionBasis_add_axisUnionBasis_subset {p q c : ℕ} (hcq : c = 0 ∨ p ≤ q)
    (hc : c ≤ e) :
    axisUnionBasis e q c + axisUnionBasis e p e ⊆ axisPoints e (q + p) ∪
      (axisPoints e q + unitVectors e e) ∪ (unitVectors e c + unitVectors e e) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  simp only [mem_union]
  obtain ha | ha := mem_union.1 ha <;> obtain hb | hb := mem_union.1 hb
  · exact Or.inl (Or.inl (axisPoints_add_axisPoints_subset q p (add_mem_add ha hb)))
  · exact Or.inl (Or.inr (add_mem_add ha hb))
  · obtain rfl | hpq := hcq
    · simp [unitVectors] at ha
    · rw [add_comm a b]
      exact Or.inl (Or.inr (add_mem_add (axisPoints_mono hpq hb) (unitVectors_mono hc ha)))
  · exact Or.inr (add_mem_add ha hb)
private lemma card_axisUnionBasis_add_le {p q c : ℕ} (hcq : c = 0 ∨ p ≤ q) (hc : c ≤ e) :
    #(axisUnionBasis e q c + axisUnionBasis e p e) ≤
      q + p + 1 + (q + 1) * e + (c + 1).choose 2 + c * (e - c) := by
  grind [card_le_card (axisUnionBasis_add_axisUnionBasis_subset hcq hc),
    card_union_le (axisPoints e (q + p) ∪ (axisPoints e q + unitVectors e e))
      (unitVectors e c + unitVectors e e),
    card_union_le (axisPoints e (q + p)) (axisPoints e q + unitVectors e e),
    card_add_le (s := axisPoints e q) (t := unitVectors e e), card_axisPoints e (q + p),
    card_axisPoints e q, card_unitVectors (e := e) le_rfl, card_unitVectors_add_le hc]
private lemma two_mul_choose_two_add_one (c : ℕ) : 2 * (c + 1).choose 2 = (c + 1) * c := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (c + 1),
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self c)]
private lemma exists_card_add_le_of_le {m n : ℕ} (hm : 1 ≤ m) (hn : e + 2 ≤ n) (hmn : m + e ≤ n) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨axisUnionBasis e a 0, axisUnionBasis e (a + r) e, by simp [card_axisUnionBasis],
    by rw [card_axisUnionBasis _ le_rfl]; grind, affineDim_axisUnionBasis (by grind), ?_⟩
  rw [sumsetCardLowerBound_of_add_le (by grind), Nat.add_sub_cancel]
  grind [card_axisUnionBasis_add_le (e := e) (p := a + r) (q := a) (Or.inl rfl) (Nat.zero_le e),
    Nat.choose_eq_zero_of_lt (by grind : 0 + 1 < 2)]
private lemma exists_card_add_le_of_lt {m n : ℕ} (hmn : m ≤ n) (hn : e + 2 ≤ n) (hnm : n < m + e) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt (by grind : t < e)
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (by grind : c + 2 ≤ m)
  refine ⟨axisUnionBasis (t + c + 1) p (c + 1), axisUnionBasis (t + c + 1) p (t + c + 1),
    by rw [card_axisUnionBasis _ (by grind)]; grind,
    by rw [card_axisUnionBasis _ le_rfl]; grind, affineDim_axisUnionBasis (by grind), ?_⟩
  have h := two_mul_sumsetCardLowerBound_add_add (d := t + c + 1 + 1) (m := c + 2 + p)
    (n := c + 2 + p + t) (by grind) (by grind) (by grind)
  rw [Nat.add_sub_cancel_left] at h
  apply (card_axisUnionBasis_add_le (Or.inr le_rfl) (by grind)).trans
  rw [(by grind : t + c + 1 - (c + 1) = t)]
  nlinarith [two_mul_choose_two_add_one (c + 1)]
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : e + 2 ≤ n) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain hmn' | hnm := le_or_gt (m + e) n
  · exact exists_card_add_le_of_le hm hn hmn'
  · exact exists_card_add_le_of_lt hmn hn hnm
end SumOfSetsInSeveralDimensions
