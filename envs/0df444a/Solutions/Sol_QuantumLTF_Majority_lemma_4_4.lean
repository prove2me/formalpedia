-- Prove2me | solution 1 for QuantumLTF.Majority.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:20:02.316244+00:00
-- url     : https://prove2.me/submissions/b2b56c3a-c58c-423f-9b33-98b62282e177

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QLTF44Aux
open QuantumLTF.Majority QAlgorithms

lemma bit_eq {n : ℕ} (A T : Finset (Fin n)) :
    majorityBit A (fun i => decide (i ∈ T)) = decide (2 * (A ∩ T).card < A.card) := by
  simp [majorityBit, Finset.filter_mem_eq_inter]

lemma dist_aux {n : ℕ} (A B : Finset (Fin n)) (hB : B.Nonempty) (hAB : (A \ B).Nonempty) :
    ∃ S : Fin n → Bool, majorityBit A S ≠ majorityBit B S := by
  classical
  have hA : A.card = (A \ B).card + (A ∩ B).card := (Finset.card_sdiff_add_card_inter A B).symm
  have hBc : B.card = (B \ A).card + (A ∩ B).card := by
    rw [Finset.inter_comm]; exact (Finset.card_sdiff_add_card_inter B A).symm
  have ha1 : 1 ≤ (A \ B).card := Finset.card_pos.mpr hAB
  have hb1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  by_cases hspec : (B \ A).card = 0 ∧ (A \ B).card = 1 ∧ (A ∩ B).card % 2 = 0
  · obtain ⟨C', hC'sub, hC'card⟩ :=
      Finset.exists_subset_card_eq (show (A ∩ B).card / 2 ≤ (A ∩ B).card by omega)
    refine ⟨fun i => decide (i ∈ C'), ?_⟩
    rw [bit_eq, bit_eq]
    have h1 : A ∩ C' = C' := Finset.inter_eq_right.mpr (hC'sub.trans Finset.inter_subset_left)
    have h2 : B ∩ C' = C' := Finset.inter_eq_right.mpr (hC'sub.trans Finset.inter_subset_right)
    rw [h1, h2, hC'card, hA, hBc]
    have e1 : 2 * ((A ∩ B).card / 2) < (A \ B).card + (A ∩ B).card := by omega
    have e2 : ¬ 2 * ((A ∩ B).card / 2) < (B \ A).card + (A ∩ B).card := by omega
    simp [e2]; omega
  · obtain ⟨C', hC'sub, hC'card⟩ :=
      Finset.exists_subset_card_eq
        (show ((A ∩ B).card + 1 - (A \ B).card) / 2 ≤ (A ∩ B).card by omega)
    refine ⟨fun i => decide (i ∈ (A \ B) ∪ C'), ?_⟩
    rw [bit_eq, bit_eq]
    have hdisj : Disjoint (A \ B) C' := by
      refine Finset.disjoint_of_subset_right hC'sub ?_
      exact Finset.disjoint_of_subset_right Finset.inter_subset_right Finset.sdiff_disjoint
    have hT : ((A \ B) ∪ C').card = (A \ B).card + ((A ∩ B).card + 1 - (A \ B).card) / 2 := by
      rw [Finset.card_union_of_disjoint hdisj, hC'card]
    have h1 : A ∩ ((A \ B) ∪ C') = (A \ B) ∪ C' :=
      Finset.inter_eq_right.mpr
        (Finset.union_subset Finset.sdiff_subset (hC'sub.trans Finset.inter_subset_left))
    have h2 : B ∩ ((A \ B) ∪ C') = C' := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxB, (⟨_, hxnB⟩ | hxC)⟩
        · exact absurd hxB hxnB
        · exact hxC
      · intro hxC
        exact ⟨(Finset.mem_inter.mp (hC'sub hxC)).2, Or.inr hxC⟩
    rw [h1, h2, hT, hC'card, hA, hBc]
    have e1 : ¬ 2 * ((A \ B).card + ((A ∩ B).card + 1 - (A \ B).card) / 2) <
        (A \ B).card + (A ∩ B).card := by omega
    have e2 : 2 * (((A ∩ B).card + 1 - (A \ B).card) / 2) < (B \ A).card + (A ∩ B).card := by
      omega
    simp [e2]; omega

end QLTF44Aux

open QuantumLTF.Majority QAlgorithms in
theorem solution : ∀ n k : ℕ, 1≤k → k≤n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X := by
  intro n k _ _
  classical
  have hdist : ∀ A B : BoundedSupports n k, A ≠ B →
      ∃ S : Qubits n, majorityBit A.1 S ≠ majorityBit B.1 S := by
    intro A B hAB
    by_cases h : (A.1 \ B.1).Nonempty
    · exact QLTF44Aux.dist_aux A.1 B.1 B.2.1 h
    · have h' : (B.1 \ A.1).Nonempty := by
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h2
        exact hAB (Subtype.ext (Finset.Subset.antisymm h h2))
      obtain ⟨S, hS⟩ := QLTF44Aux.dist_aux B.1 A.1 A.2.1 h'
      exact ⟨S, fun e => hS e.symm⟩
  choose pick hpick using hdist
  let v : BoundedSupports n k → BoundedSupports n k → BoundedSupports n k → ℝ :=
    fun A B C => if C = A ∨ C = B then 1 else 0
  let c : Qubits n → BoundedSupports n k × BoundedSupports n k → ℝ :=
    fun S p => if h : p.1 ≠ p.2 then (if pick p.1 p.2 h = S then 1/2 else 0) else 0
  refine ⟨fun S => ∑ p, c S p • Matrix.vecMulVec (v p.1 p.2) (v p.1 p.2), ?_, ?_⟩
  · intro S
    refine Matrix.posSemidef_sum _ (fun p _ => ?_)
    have hc : 0 ≤ c S p := by simp only [c]; split_ifs <;> norm_num
    have := Matrix.posSemidef_vecMulVec_self_star (v p.1 p.2)
    rw [star_trivial] at this
    exact this.smul hc
  · intro A B hAB
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    rw [← Finset.sum_filter, Finset.sum_comm]
    rw [Fintype.sum_eq_add (A, B) (B, A)]
    · have key1 : ∑ x with majorityBit (↑A) x ≠ majorityBit (↑B) x,
          c x (A, B) * (v (A, B).1 (A, B).2 A * v (A, B).1 (A, B).2 B) = 1 / 2 := by
        rw [Finset.sum_eq_single (pick A B hAB)]
        · simp [c, v, hAB]
        · intro S _ hS
          have hne : pick A B hAB ≠ S := fun e => hS e.symm
          simp [c, hAB, hne]
        · intro hnot; exfalso; apply hnot
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hpick A B hAB
      have key2 : ∑ x with majorityBit (↑A) x ≠ majorityBit (↑B) x,
          c x (B, A) * (v (B, A).1 (B, A).2 A * v (B, A).1 (B, A).2 B) = 1 / 2 := by
        rw [Finset.sum_eq_single (pick B A (Ne.symm hAB))]
        · simp [c, v, Ne.symm hAB]
        · intro S _ hS
          have hne : pick B A (Ne.symm hAB) ≠ S := fun e => hS e.symm
          simp [c, Ne.symm hAB, hne]
        · intro hnot; exfalso; apply hnot
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun e => hpick B A (Ne.symm hAB) e.symm
      rw [key1, key2]; norm_num
    · exact fun h => hAB (congrArg Prod.fst h)
    · rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      apply Finset.sum_eq_zero
      intro S _
      have hv : v p1 p2 A * v p1 p2 B = 0 := by
        simp only [v]
        by_cases h1 : A = p1 ∨ A = p2
        · by_cases h2 : B = p1 ∨ B = p2
          · exfalso
            rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
            · exact hAB rfl
            · exact hp1 rfl
            · exact hp2 rfl
            · exact hAB rfl
          · simp [h2]
        · simp [h1]
      simp only at hv ⊢
      rw [hv, mul_zero]
