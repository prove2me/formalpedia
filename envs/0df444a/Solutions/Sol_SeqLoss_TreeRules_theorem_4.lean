-- Prove2me | solution 1 for SeqLoss.TreeRules.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:17:20.907309+00:00
-- url     : https://prove2.me/submissions/667a8ac4-8481-4ca1-acb3-6e18d73710dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms
import Theorems.Thm_SeqLoss_TreeRules_proposition_3
import Theorems.Thm_SeqLoss_TreeRules_proposition_2_trees
import Theorems.Thm_SeqLoss_TreeRules_fixedFractionTree_isTreeRule

namespace SeqLoss.TreeRules

open Finset

theorem treeChain_mem' {n : ℕ} {e : ℕ × ℕ} :
    e ∈ treeChain n ↔ 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.2 = e.1 + 1 := by
  unfold treeChain
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨e.1, ⟨h1, h2⟩, by ext <;> simp [h3]⟩

theorem N_treeChain' (n : ℕ) : N (treeChain n) = Icc 1 n := by
  ext i
  unfold N
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨e, he, rfl⟩; rw [treeChain_mem'] at he; exact ⟨he.1, he.2.1⟩
  · rintro ⟨h1, h2⟩; exact ⟨(i, i + 1), treeChain_mem'.2 ⟨h1, h2, rfl⟩, rfl⟩

theorem V_treeChain' {n : ℕ} (hn : 1 ≤ n) : V (treeChain n) = Icc 1 (n + 1) := by
  ext v
  unfold V
  simp only [mem_union, mem_image, mem_Icc]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) <;> rw [treeChain_mem'] at he <;> omega
  · rintro ⟨h1, h2⟩
    by_cases hv : v ≤ n
    · exact Or.inl ⟨(v, v + 1), treeChain_mem'.2 ⟨h1, hv, rfl⟩, rfl⟩
    · refine Or.inr ⟨(v - 1, v), treeChain_mem'.2 ⟨by omega, by omega, by simp; omega⟩, rfl⟩

theorem isTree_treeChain' {n : ℕ} (hn : 1 ≤ n) : IsTree (treeChain n) := by
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rw [V_treeChain' hn, mem_Icc]; omega
  · intro e he; rw [treeChain_mem'] at he; omega
  · intro v hv hv1
    rw [V_treeChain' hn, mem_Icc] at hv
    refine ⟨v - 1, treeChain_mem'.2 ⟨by simp; omega, by simp; omega, by simp; omega⟩, ?_⟩
    intro u hu
    rw [treeChain_mem'] at hu
    simp at hu; omega
  · intro v hv
    rw [V_treeChain' hn, mem_Icc] at hv
    obtain ⟨h1, h2⟩ := hv
    induction v with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail (ih (by omega) (by omega))
          (show Edge (treeChain n) k (k + 1) from treeChain_mem'.2 ⟨by omega, by omega, rfl⟩)

/-- The fixed-fraction rule is additive. -/
theorem fixedFractionTree_additive (lam : ℝ) : TreeAdditive (fixedFractionTree lam) := by
  intro T _ ℓ ℓ' _ _ i _
  unfold fixedFractionTree
  simp only [Pi.add_apply, sum_add_distrib]
  split_ifs <;> ring

/-- The fixed-fraction rule satisfies zero truncation. -/
theorem fixedFractionTree_zeroTruncation (lam : ℝ) : TreeZeroTruncation (fixedFractionTree lam) := by
  intro T _ ℓ _ e _ he2 he0 i hi
  have heT : e ∉ T := by
    intro h; apply he2; unfold V; exact mem_union_right _ (mem_image_of_mem _ h)
  have hiV : i ∈ V T := by unfold V; exact mem_union_left _ hi
  have hei : e.2 ≠ i := fun h => he2 (h ▸ hiV)
  unfold fixedFractionTree
  rw [sum_insert heT, he0, zero_add, filter_insert]
  have hs : ∑ x ∈ (if e.1 = i then insert e (T.filter fun e => e.1 = i) else
      T.filter fun e => e.1 = i), ℓ x = ∑ x ∈ T.filter (fun e => e.1 = i), ℓ x := by
    split_ifs
    · rw [sum_insert (fun h => heT (mem_filter.1 h).1), he0, zero_add]
    · rfl
  rw [hs]
  have hr : (∀ x ∈ insert e T, x.2 ≠ i) ↔ ∀ x ∈ T, x.2 ≠ i := by
    rw [forall_mem_insert]; exact ⟨fun h => h.2, fun h => ⟨hei, h⟩⟩
  simp only [hr]

/-- On the path order: a descendant has at least the depth of its ancestor. -/
theorem depth_le_of_reach (T : Finset (ℕ × ℕ)) {i v : ℕ}
    (h : Relation.ReflTransGen (Edge T) i v) : depth T i ≤ depth T v := by
  unfold depth pathTo
  apply Nat.add_le_add_right
  apply card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  exact ⟨he.1, he.2.trans h⟩

end SeqLoss.TreeRules

open SeqLoss.TreeRules Finset

theorem solution (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ) :
    (TreeAdditive φ ∧ TreeZeroTruncation φ ∧ TreeMergingProof φ ∧ TreePopulationMonotone φ) ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ → ∀ i ∈ N T,
        φ T ℓ i = fixedFractionTree lam T ℓ i := by
  constructor
  · rintro ⟨hadd, hzt, hmp, hpm⟩
    obtain ⟨lam, hlam, hchain⟩ := (proposition_2_trees φ hφ).1 ⟨hpm, hmp⟩
    refine ⟨lam, hlam, fun T hT ℓ hℓ i hi => ?_⟩
    have hexp := (proposition_3 φ hφ).1 ⟨hadd, hzt⟩ T hT ℓ hℓ i hi
    have hexpL := (proposition_3 (fixedFractionTree lam) (fixedFractionTree_isTreeRule lam hlam)).1
      ⟨fixedFractionTree_additive lam, fixedFractionTree_zeroTruncation lam⟩ T hT ℓ hℓ i hi
    rw [hexp, hexpL]
    refine sum_congr rfl (fun e he => ?_)
    congr 1
    apply hchain _ (by unfold depth; omega)
    rw [mem_Icc]
    refine ⟨by unfold depth; omega, depth_le_of_reach T ?_⟩
    simp only [subtreeAt, mem_filter] at he
    exact he.2
  · rintro ⟨lam, hlam, h⟩
    have hchain : ∀ n : ℕ, 1 ≤ n → ∀ i ∈ Finset.Icc 1 n,
        φ (treeChain n) (chainLoss n) i = fixedFractionTree lam (treeChain n) (chainLoss n) i := by
      intro n hn i hi
      refine h _ (isTree_treeChain' hn) _ ?_ i (by rw [N_treeChain']; exact hi)
      intro e; unfold chainLoss; split_ifs <;> norm_num
    obtain ⟨hpm, hmp⟩ := (proposition_2_trees φ hφ).2 ⟨lam, hlam, hchain⟩
    refine ⟨?_, ?_, hmp, hpm⟩
    · intro T hT ℓ ℓ' hℓ hℓ' i hi
      have hsum : IsTreeLoss (ℓ + ℓ') := fun e => add_nonneg (hℓ e) (hℓ' e)
      rw [h T hT ℓ hℓ i hi, h T hT ℓ' hℓ' i hi, h T hT _ hsum i hi]
      exact fixedFractionTree_additive lam T hT ℓ ℓ' hℓ hℓ' i hi
    · intro T hT ℓ hℓ e hTe he2 he0 i hi
      have hi' : i ∈ N (insert e T) := by
        unfold N at hi ⊢; rw [image_insert]; exact mem_insert_of_mem hi
      rw [h T hT ℓ hℓ i hi, h _ hTe ℓ hℓ i hi']
      exact fixedFractionTree_zeroTruncation lam T hT ℓ hℓ e hTe he2 he0 i hi
