-- Prove2me | solution 1 for PosetMarginals.Chains.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:34:32.594398+00:00
-- url     : https://prove2.me/submissions/487fa401-75c1-4b15-ab04-fbb231a43e99

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model
import Definitions.Def_PosetMarginals_Chains_Algorithm
import Theorems.Thm_PosetMarginals_Chains_proposition_3
import Theorems.Thm_PosetMarginals_Chains_proposition_4

open Classical PosetMarginals.Chains

namespace PMThm2

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Equation (7)/(8) of the paper. -/
lemma key_identity (σ : Finset α → ℝ) (ρ : α → ℝ)
    (hmarg : ∀ x, ∑ S ∈ Finset.univ.filter (fun S : Finset α => x ∈ S), σ S = ρ x)
    (C : Finset α) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset α => (S ∩ C).Nonempty), σ S) +
      (∑ S ∈ Finset.univ.filter (fun S : Finset α => 2 ≤ (S ∩ C).card),
        σ S * (((S ∩ C).card : ℝ) - 1)) = ∑ x ∈ C, ρ x := by
  classical
  have h1 : ∑ x ∈ C, ρ x = ∑ S : Finset α, σ S * ((S ∩ C).card : ℝ) := by
    calc ∑ x ∈ C, ρ x
        = ∑ x ∈ C, ∑ S : Finset α, (if x ∈ S then σ S else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← hmarg x, Finset.sum_filter]
      _ = ∑ S : Finset α, ∑ x ∈ C, (if x ∈ S then σ S else 0) := Finset.sum_comm
      _ = ∑ S : Finset α, σ S * ((S ∩ C).card : ℝ) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.inter_comm]
          ring
  rw [h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rcases Nat.lt_or_ge ((S ∩ C).card) 2 with h | h
  · interval_cases hc : (S ∩ C).card
    · have : ¬ (S ∩ C).Nonempty := by
        rw [← Finset.card_pos, hc]; omega
      simp [this]
    · have : (S ∩ C).Nonempty := by
        rw [← Finset.card_pos, hc]; omega
      simp [this]
  · have : (S ∩ C).Nonempty := by
      rw [← Finset.card_pos]; omega
    simp only [this, if_true, h]
    ring

lemma hit_iff (σ : Finset α → ℝ) (ρ : α → ℝ) (π : Finset α → ℝ)
    (hmarg : ∀ x, ∑ S ∈ Finset.univ.filter (fun S : Finset α => x ∈ S), σ S = ρ x)
    (C : Finset α) :
    π C ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset α => (S ∩ C).Nonempty), σ S ↔
      ∑ S ∈ Finset.univ.filter (fun S : Finset α => 2 ≤ (S ∩ C).card),
        σ S * (((S ∩ C).card : ℝ) - 1) ≤ delta ρ π C := by
  have := key_identity σ ρ hmarg C
  unfold delta
  constructor <;> intro h <;> linarith

end PMThm2

open PMThm2 in
theorem solution {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    zQ ρ π = maxValue ρ π := by
  obtain ⟨n, hn, hpre, hfeas⟩ := proposition_3 ρ π h
  have h4 := proposition_4 ρ π h n hn hpre
  have hsum : ∑ S, output ρ π n S = maxValue ρ π := by
    rw [← h4]
    unfold output
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_ite_eq]
    simp
  -- lower bound: every feasible value of (Q) is at least maxValue
  have hlow : ∀ σ, FeasibleQ ρ π σ → maxValue ρ π ≤ ∑ S, σ S := by
    rintro σ ⟨hpos, hmarg, hcon⟩
    unfold maxValue
    apply csSup_le
    · exact ⟨ρ (Classical.arbitrary α), Or.inl ⟨_, rfl⟩⟩
    · rintro v (⟨x, rfl⟩ | ⟨C, hC, rfl⟩)
      · rw [← hmarg x]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ => hpos S)
      · have := (hit_iff σ ρ π hmarg C).2 (hcon C hC)
        refine this.trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ => hpos S)
  apply le_antisymm
  · rw [← hsum]
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro v ⟨σ, hσ, rfl⟩
      exact Finset.sum_nonneg (fun S _ => hσ.1 S)
    · exact ⟨_, hfeas, rfl⟩
  · apply le_csInf
    · exact ⟨_, _, hfeas, rfl⟩
    · rintro v ⟨σ, hσ, rfl⟩
      exact hlow σ hσ
