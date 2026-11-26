-- Prove2me | solution 1 for SemigroupBetti.IsPairAntichain.exists_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:36.852219+00:00
-- url     : https://prove2.me/submissions/ec259dc2-0d4e-402d-b9e8-19f0a9d7d3f8

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_fst_inj
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_rank_le
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_corank_le
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}
namespace SemigroupBetti
namespace IsPairAntichain
theorem _root_.solution (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ T.card) :
    ∃ x ∈ T, r ≤ x.1 ∧ T.card + 1 - r ≤ x.2 := by
  classical
  let rk : ℕ × ℕ → ℕ := fun x => (T.filter (fun y => y.1 ≤ x.1)).card
  have hmaps : ∀ x (hx : x ∈ T), rk x ∈ Icc 1 T.card := by
    intro x hx
    refine mem_Icc.2 ⟨card_pos.2 ⟨x, mem_filter.2 ⟨hx, le_rfl⟩⟩, card_le_card (filter_subset _ _)⟩
  have hinj : ∀ x y (hx : x ∈ T) (hy : y ∈ T), rk x = rk y → x = y := by
    intro x y hx hy h
    by_contra hne
    have hne1 : x.1 ≠ y.1 := fun h1 => hne (hT.fst_inj hx hy h1)
    rcases Nat.lt_or_gt_of_ne hne1 with hlt | hlt
    · have : (T.filter (fun z => z.1 ≤ x.1)) ⊂ (T.filter (fun z => z.1 ≤ y.1)) := by
        refine ⟨fun z hz => ?_, fun hsub => ?_⟩
        · have := mem_filter.1 hz; exact mem_filter.2 ⟨this.1, by omega⟩
        · have := (mem_filter.1 (hsub (mem_filter.2 ⟨hy, le_rfl⟩))).2; omega
      have := card_lt_card this; simp only [rk] at h; omega
    · have : (T.filter (fun z => z.1 ≤ y.1)) ⊂ (T.filter (fun z => z.1 ≤ x.1)) := by
        refine ⟨fun z hz => ?_, fun hsub => ?_⟩
        · have := mem_filter.1 hz; exact mem_filter.2 ⟨this.1, by omega⟩
        · have := (mem_filter.1 (hsub (mem_filter.2 ⟨hx, le_rfl⟩))).2; omega
      have := card_lt_card this; simp only [rk] at h; omega
  obtain ⟨x, hx, hxr⟩ := surj_on_of_inj_on_of_card_le (fun x _ => rk x) hmaps hinj
    (by simp) r (mem_Icc.2 ⟨hr1, hrk⟩)
  refine ⟨x, hx, ?_, ?_⟩
  · have := hT.rank_le hpos (x := x); simp only [rk] at hxr; omega
  · have hunion : T.filter (fun y => y.1 ≤ x.1) ∪ T.filter (fun y => x.1 ≤ y.1) = T := by
      ext y; simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hy; rcases le_total y.1 x.1 with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    have hinter : T.filter (fun y => y.1 ≤ x.1) ∩ T.filter (fun y => x.1 ≤ y.1) = {x} := by
      ext y; simp only [mem_inter, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨hy, h1⟩, -, h2⟩; exact hT.fst_inj hy hx (le_antisymm h1 h2)
      · rintro rfl; exact ⟨⟨hx, le_rfl⟩, hx, le_rfl⟩
    have hsum := card_union_add_card_inter (T.filter (fun y => y.1 ≤ x.1))
      (T.filter (fun y => x.1 ≤ y.1))
    rw [hunion, hinter, card_singleton] at hsum
    have := hT.corank_le hpos hx
    simp only [rk] at hxr
    omega
end IsPairAntichain
end SemigroupBetti
