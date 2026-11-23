-- Prove2me | solution 1 for card_block_eq_m_of_foldable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:39:04.270291+00:00
-- url     : https://prove2.me/submissions/22d263dd-82c9-44d3-967b-0809d3045310

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_card_block_le_m
import Theorems.Thm_foldable_pow_domain_card


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (D : Finset F) (m : ℕ) (hm : m > 0) (z : F)
    (hz : z ∈ pow_domain D m) (h_foldable : IsFoldable D m) :
    (Block D m z).card = m := by
  have h_card_eq := foldable_pow_domain_card D m h_foldable
  have h_sum_eq : ∑ z' ∈ pow_domain D m, (Block D m z').card = D.card := by
    rw [← Finset.card_biUnion]
    · congr with x; simp only [pow_domain, Block, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_filter, and_iff_right_iff_imp, exists_eq_right_right']
      exact fun hx ↦ ⟨x, hx, rfl⟩
    · intro x hx y hy hxy; grind [Finset.disjoint_left, Block]
  have h_card_le : ∀ z' ∈ pow_domain D m, (Block D m z').card ≤ m :=
    fun z' _ ↦ card_block_le_m D m z' hm
  contrapose! h_card_eq
  exact h_sum_eq ▸
    (Finset.sum_lt_sum h_card_le
      ⟨z, hz, (h_card_le z hz).lt_of_ne h_card_eq⟩).trans_le (by simp [mul_comm]) |>.ne
