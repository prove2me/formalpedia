-- Prove2me | solution 1 for SeqLoss.TreeRules.proposition_2_trees
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:15:28.189333+00:00
-- url     : https://prove2.me/submissions/441d0a36-482a-4947-b610-fa235201e02f

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

open Finset

theorem treeChain_mem {n : ℕ} {e : ℕ × ℕ} :
    e ∈ treeChain n ↔ 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.2 = e.1 + 1 := by
  unfold treeChain
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨e.1, ⟨h1, h2⟩, by ext <;> simp [h3]⟩

theorem N_treeChain (n : ℕ) : N (treeChain n) = Icc 1 n := by
  ext i
  unfold N
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨e, he, rfl⟩; rw [treeChain_mem] at he; exact ⟨he.1, he.2.1⟩
  · rintro ⟨h1, h2⟩; exact ⟨(i, i + 1), treeChain_mem.2 ⟨h1, h2, rfl⟩, rfl⟩

theorem V_treeChain {n : ℕ} (hn : 1 ≤ n) : V (treeChain n) = Icc 1 (n + 1) := by
  ext v
  unfold V
  simp only [mem_union, mem_image, mem_Icc]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) <;> rw [treeChain_mem] at he <;> omega
  · rintro ⟨h1, h2⟩
    by_cases hv : v ≤ n
    · exact Or.inl ⟨(v, v + 1), treeChain_mem.2 ⟨h1, hv, rfl⟩, rfl⟩
    · refine Or.inr ⟨(v - 1, v), treeChain_mem.2 ⟨by omega, by omega, by simp; omega⟩, rfl⟩

theorem isTree_treeChain {n : ℕ} (hn : 1 ≤ n) : IsTree (treeChain n) := by
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rw [V_treeChain hn, mem_Icc]; omega
  · intro e he; rw [treeChain_mem] at he; omega
  · intro v hv hv1
    rw [V_treeChain hn, mem_Icc] at hv
    refine ⟨v - 1, treeChain_mem.2 ⟨by simp; omega, by simp; omega, by simp; omega⟩, ?_⟩
    intro u hu
    rw [treeChain_mem] at hu
    simp at hu; omega
  · intro v hv
    rw [V_treeChain hn, mem_Icc] at hv
    obtain ⟨h1, h2⟩ := hv
    induction v with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail (ih (by omega) (by omega))
          (show Edge (treeChain n) k (k + 1) from treeChain_mem.2 ⟨by omega, by omega, rfl⟩)

theorem isTreeLoss_chainLoss (n : ℕ) : IsTreeLoss (chainLoss n) := by
  intro e; unfold chainLoss; split_ifs <;> norm_num

theorem sum_chainLoss {n : ℕ} (hn : 1 ≤ n) : ∑ e ∈ treeChain n, chainLoss n e = 1 := by
  unfold treeChain
  rw [sum_image (by intro a _ b _ h; simpa using h)]
  simp only [chainLoss, Prod.mk.injEq, and_self, add_left_inj]
  rw [sum_ite_eq' (Icc 1 n) n (fun _ => (1 : ℝ))]
  simp [mem_Icc]; omega

theorem sum_chainLoss_filter (n i : ℕ) :
    ∑ e ∈ (treeChain n).filter (fun e => e.1 = i), chainLoss n e =
      if i ∈ Icc 1 n ∧ i = n then 1 else 0 := by
  rw [sum_filter]
  unfold treeChain
  rw [sum_image (by intro a _ b _ h; simpa using h)]
  simp only [chainLoss, Prod.mk.injEq, and_self, add_left_inj]
  have : ∀ j ∈ Icc 1 n, ((if j = i then (if j = n then (1 : ℝ) else 0) else 0)) =
      if j = i then (if i = n then 1 else 0) else 0 := by
    intro j _; split_ifs <;> simp_all
  rw [sum_congr rfl this, sum_ite_eq' (Icc 1 n) i (fun _ => if i = n then (1 : ℝ) else 0)]
  split_ifs <;> simp_all

theorem fixedFraction_chain (lam : ℝ) {n i : ℕ} (hi : i ∈ Icc 1 n) :
    fixedFractionTree lam (treeChain n) (chainLoss n) i =
      (if i = n then lam else 0) + (if i = 1 then 1 - lam else 0) := by
  have hn : 1 ≤ n := by rw [mem_Icc] at hi; omega
  unfold fixedFractionTree
  rw [sum_chainLoss_filter, sum_chainLoss hn]
  have hroot : (∀ e ∈ treeChain n, e.2 ≠ i) ↔ i = 1 := by
    rw [mem_Icc] at hi
    constructor
    · intro h
      by_contra h1
      exact h (i - 1, i) (treeChain_mem.2 ⟨by simp; omega, by simp; omega, by simp; omega⟩) rfl
    · rintro rfl e he; rw [treeChain_mem] at he; omega
  have hin : i ∈ Icc 1 n := hi
  by_cases h1 : i = 1
  · rw [if_pos (hroot.2 h1)]
    by_cases h2 : i = n
    · rw [if_pos ⟨hin, h2⟩, if_pos h2, if_pos h1]; ring
    · rw [if_neg (fun h => h2 h.2), if_neg h2, if_pos h1]; ring
  · rw [if_neg (mt hroot.1 h1), if_neg h1]
    by_cases h2 : i = n
    · rw [if_pos ⟨hin, h2⟩, if_pos h2]; ring
    · rw [if_neg (fun h => h2 h.2), if_neg h2]; ring

theorem proposition_2_trees_aux (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) :
    (TreePopulationMonotone φ ∧ TreeMergingProof φ) ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n → ∀ i ∈ Finset.Icc 1 n,
        φ (treeChain n) (chainLoss n) i =
          fixedFractionTree lam (treeChain n) (chainLoss n) i := by
  set x : ℕ → ℕ → ℝ := fun n i => φ (treeChain n) (chainLoss n) i with hx
  have nonneg : ∀ n, 1 ≤ n → ∀ i ∈ Icc 1 n, 0 ≤ x n i := by
    intro n hn i hi
    have := (hφ _ (isTree_treeChain hn) _ (isTreeLoss_chainLoss n)).1 i (by rw [N_treeChain]; exact hi)
    exact this
  have total : ∀ n, 1 ≤ n → ∑ i ∈ Icc 1 n, x n i = 1 := by
    intro n hn
    have := (hφ _ (isTree_treeChain hn) _ (isTreeLoss_chainLoss n)).2.1
    rw [N_treeChain, sum_chainLoss hn] at this
    exact this
  constructor
  · rintro ⟨hpm, hmp⟩
    have t1 := total 1 le_rfl
    have t2 := total 2 (by norm_num)
    have t3 := total 3 (by norm_num)
    simp only [show Icc 1 1 = {1} by rfl, show Icc 1 2 = {1, 2} by rfl,
      show Icc 1 3 = {1, 2, 3} by rfl] at t1 t2 t3
    rw [sum_singleton] at t1
    rw [sum_insert (by simp), sum_singleton] at t2
    rw [sum_insert (by simp), sum_insert (by simp), sum_singleton] at t3
    have n21 := nonneg 2 (by norm_num) 1 (by simp)
    have n22 := nonneg 2 (by norm_num) 2 (by simp)
    have n31 := nonneg 3 (by norm_num) 1 (by simp)
    have n32 := nonneg 3 (by norm_num) 2 (by simp)
    have n33 := nonneg 3 (by norm_num) 3 (by simp)
    have m1 : x 3 1 + x 3 2 ≤ x 2 1 := hmp 1 (by simp)
    have m2 : x 3 2 + x 3 3 ≤ x 2 2 := hmp 2 (by simp)
    set lam := x 2 2 with hlam
    refine ⟨lam, ⟨n22, by linarith⟩, ?_⟩
    -- the claim for all n ≥ 3, by induction
    have key : ∀ n, 3 ≤ n → ∀ i ∈ Icc 1 n,
        x n i = (if i = n then lam else 0) + (if i = 1 then 1 - lam else 0) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        intro i hi
        have e32 : x 3 2 = 0 := by linarith
        simp only [mem_Icc] at hi
        have : i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl
        · rw [if_neg (by norm_num), if_pos rfl, zero_add]; linarith
        · rw [if_neg (by norm_num), if_neg (by norm_num), add_zero]; exact e32
        · rw [if_pos rfl, if_neg (by norm_num), add_zero]; linarith
      | succ n hn ih =>
        have up1 : ∀ i, 1 ≤ i → i ≤ n - 1 → x (n + 1) i ≤ x n i := fun i h1 h2 =>
          (hpm n i i n (by omega) (by omega) h1 le_rfl (by omega) le_rfl).1
        have up2 : ∀ k, 2 ≤ k → k ≤ n → x (n + 1) (k + 1) ≤ x n k := fun k h1 h2 =>
          (hpm n (k - 1) 1 k (by omega) (by omega) le_rfl (by omega) (by omega) h2).2
        have mid : ∀ i, 2 ≤ i → i ≤ n → x (n + 1) i = 0 := by
          intro i h1 h2
          have hnn := nonneg (n + 1) (by omega) i (by rw [mem_Icc]; omega)
          by_cases hi : i ≤ n - 1
          · have := up1 i (by omega) hi
            rw [ih i (by rw [mem_Icc]; omega), if_neg (by omega), if_neg (by omega)] at this
            linarith
          · have := up2 (i - 1) (by omega) (by omega)
            rw [show i - 1 + 1 = i by omega, ih (i - 1) (by rw [mem_Icc]; omega),
              if_neg (by omega), if_neg (by omega)] at this
            linarith
        have e1 := up1 1 le_rfl (by omega)
        rw [ih 1 (by rw [mem_Icc]; omega), if_neg (by omega), if_pos rfl] at e1
        have e2 := up2 n (by omega) le_rfl
        rw [ih n (by rw [mem_Icc]; omega), if_pos rfl, if_neg (by omega)] at e2
        have tot := total (n + 1) (by omega)
        have hsub : ({1, n + 1} : Finset ℕ) ⊆ Icc 1 (n + 1) := by
          intro i hi; simp at hi; rw [mem_Icc]; omega
        rw [← sum_subset hsub (fun i hi hni => by
          simp only [mem_insert, mem_singleton, not_or] at hni
          rw [mem_Icc] at hi
          exact mid i (by omega) (by omega))] at tot
        rw [sum_insert (by simp; omega), sum_singleton] at tot
        intro i hi
        rw [mem_Icc] at hi
        by_cases hi1 : i = 1
        · subst hi1; rw [if_neg (by omega), if_pos rfl, zero_add]; linarith
        · by_cases hin : i = n + 1
          · subst hin; rw [if_pos rfl, if_neg (by omega), add_zero]; linarith
          · rw [mid i (by omega) (by omega), if_neg hin, if_neg hi1]; simp
    intro n hn i hi
    rw [fixedFraction_chain lam hi]
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · have : i = 1 := by rw [mem_Icc] at hi; omega
      subst this; rw [if_pos rfl, if_pos rfl]; change x 1 1 = _; linarith
    · rw [mem_Icc] at hi
      have : i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl
      · rw [if_neg (by norm_num), if_pos rfl, zero_add]; change x 2 1 = 1 - x 2 2; linarith
      · rw [if_pos rfl, if_neg (by norm_num), add_zero]
    · exact key n h3 i hi
  · rintro ⟨lam, -, hlam⟩
    have hv : ∀ n, 1 ≤ n → ∀ i ∈ Icc 1 n,
        x n i = (if i = n then lam else 0) + (if i = 1 then 1 - lam else 0) := by
      intro n hn i hi
      change φ (treeChain n) (chainLoss n) i = _
      rw [hlam n hn i hi, fixedFraction_chain lam hi]
    refine ⟨fun n j i k h1 h2 h3 h4 h5 h6 => ⟨?_, ?_⟩, fun i hi => ?_⟩
    · change x (n + 1) i ≤ x n i
      rw [hv (n + 1) (by omega) i (by rw [mem_Icc]; omega), hv n (by omega) i (by rw [mem_Icc]; omega),
        if_neg (show i ≠ n + 1 by omega), if_neg (show i ≠ n by omega)]
    · change x (n + 1) (k + 1) ≤ x n k
      rw [hv (n + 1) (by omega) (k + 1) (by rw [mem_Icc]; omega),
        hv n (by omega) k (by rw [mem_Icc]; omega), if_neg (show k + 1 ≠ 1 by omega),
        if_neg (show k ≠ 1 by omega)]
      by_cases hk : k = n
      · subst hk; simp
      · rw [if_neg (by omega), if_neg hk]
    · change x 3 i + x 3 (i + 1) ≤ x 2 i
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · rw [hv 3 (by norm_num) 1 (by simp), hv 3 (by norm_num) 2 (by simp),
          hv 2 (by norm_num) 1 (by simp)]
        simp
      · rw [hv 3 (by norm_num) 2 (by simp), hv 3 (by norm_num) 3 (by simp),
          hv 2 (by norm_num) 2 (by simp)]
        simp

end SeqLoss.TreeRules

open SeqLoss.TreeRules

theorem solution (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) :
    (TreePopulationMonotone φ ∧ TreeMergingProof φ) ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n → ∀ i ∈ Finset.Icc 1 n,
        φ (treeChain n) (chainLoss n) i =
          fixedFractionTree lam (treeChain n) (chainLoss n) i :=
  proposition_2_trees_aux φ hφ
