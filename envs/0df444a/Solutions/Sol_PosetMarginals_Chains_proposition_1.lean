-- Prove2me | solution 1 for PosetMarginals.Chains.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:33:51.159472+00:00
-- url     : https://prove2.me/submissions/789da1e8-5ffe-4ae2-bd38-af58174d9142

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

open Classical PosetMarginals.Chains

namespace PMProp1

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

end PMProp1

open PMProp1 in
theorem solution {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    ProblemD ρ π ↔ zQ ρ π ≤ 1 := by
  classical
  obtain ⟨hρ, _hπ1, h2, _h3⟩ := h
  -- the feasible set of (Q) is bounded below by 0
  have hbdd : BddBelow {v : ℝ | ∃ σ, FeasibleQ ρ π σ ∧ ∑ S, σ S = v} := by
    refine ⟨0, ?_⟩
    rintro v ⟨σ, hσ, rfl⟩
    exact Finset.sum_nonneg (fun S _ => hσ.1 S)
  constructor
  · rintro ⟨σ, hpos, hmarg, hhit, hsum⟩
    apply csInf_le hbdd
    refine ⟨σ, ⟨hpos, hmarg, fun C hC => (hit_iff σ ρ π hmarg C).1 (hhit C hC)⟩, hsum⟩
  · intro hz
    -- trivial feasible solution σ̃
    let σ0 : Finset α → ℝ := fun S => ∑ x, if S = {x} then ρ x else 0
    have hσ0 : FeasibleQ ρ π σ0 := by
      refine ⟨fun S => Finset.sum_nonneg (fun x _ => ?_), fun x => ?_, fun C hC => ?_⟩
      · split_ifs
        · exact (hρ x).1
        · exact le_refl 0
      · simp only [σ0]
        rw [Finset.sum_comm]
        rw [Finset.sum_eq_single x]
        · rw [Finset.sum_eq_single {x}]
          · simp
          · intro S _ hS; simp [hS]
          · intro hx; simp at hx
        · intro y _ hyx
          refine Finset.sum_eq_zero (fun S hS => ?_)
          simp only [Finset.mem_filter] at hS
          rw [if_neg]
          rintro rfl
          simp at hS
          exact hyx hS.symm
        · intro hx; simp at hx
      · have : ∑ S ∈ Finset.univ.filter (fun S : Finset α => 2 ≤ (S ∩ C).card),
            σ0 S * (((S ∩ C).card : ℝ) - 1) = 0 := by
          refine Finset.sum_eq_zero (fun S hS => ?_)
          simp only [Finset.mem_filter] at hS
          have : σ0 S = 0 := by
            refine Finset.sum_eq_zero (fun x _ => ?_)
            rw [if_neg]
            rintro rfl
            have := Finset.card_le_card (Finset.inter_subset_left (s₁ := {x}) (s₂ := C))
            simp at this
            omega
          rw [this, zero_mul]
        rw [this]
        unfold delta
        linarith [h2 C hC]
    set M : ℝ := ∑ S, σ0 S
    let K : Set (Finset α → ℝ) := {σ | FeasibleQ ρ π σ ∧ ∑ S, σ S ≤ M}
    have hKne : K.Nonempty := ⟨σ0, hσ0, le_refl _⟩
    have hKc : IsCompact K := by
      apply Metric.isCompact_of_isClosed_isBounded
      · have : K = (⋂ S, {σ : Finset α → ℝ | 0 ≤ σ S}) ∩
            (⋂ x, {σ : Finset α → ℝ |
              ∑ S ∈ Finset.univ.filter (fun S : Finset α => x ∈ S), σ S = ρ x}) ∩
            (⋂ C ∈ maxChains α, {σ : Finset α → ℝ |
              ∑ S ∈ Finset.univ.filter (fun S : Finset α => 2 ≤ (S ∩ C).card),
                σ S * (((S ∩ C).card : ℝ) - 1) ≤ delta ρ π C}) ∩
            {σ | ∑ S, σ S ≤ M} := by
          ext σ
          simp [K, FeasibleQ, and_assoc]
        rw [this]
        refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
        · exact isClosed_iInter (fun S => isClosed_le continuous_const (continuous_apply S))
        · exact isClosed_iInter (fun x => isClosed_eq
            (continuous_finsetSum _ (fun S _ => continuous_apply S)) continuous_const)
        · exact isClosed_biInter (fun C _ => isClosed_le
            (continuous_finsetSum _ (fun S _ => (continuous_apply S).mul continuous_const))
            continuous_const)
        · exact isClosed_le (continuous_finsetSum _ (fun S _ => continuous_apply S))
            continuous_const
      · refine (Metric.isBounded_Icc (0 : Finset α → ℝ) (fun _ => M)).subset ?_
        rintro σ ⟨hσ, hM⟩
        refine ⟨fun S => hσ.1 S, fun S => ?_⟩
        calc σ S ≤ ∑ T, σ T :=
              Finset.single_le_sum (fun T _ => hσ.1 T) (Finset.mem_univ S)
          _ ≤ M := hM
    obtain ⟨σs, hσsK, hmin⟩ := hKc.exists_isMinOn hKne
      (continuous_finsetSum _ (fun S _ => continuous_apply S)).continuousOn
    have hzeq : zQ ρ π = ∑ S, σs S := by
      apply IsLeast.csInf_eq
      refine ⟨⟨σs, hσsK.1, rfl⟩, ?_⟩
      rintro v ⟨σ, hσ, rfl⟩
      by_cases hσM : ∑ S, σ S ≤ M
      · exact hmin ⟨hσ, hσM⟩
      · push Not at hσM
        linarith [hσsK.2]
    obtain ⟨hpos, hmarg, hcon⟩ := hσsK.1
    refine ⟨fun S => σs S + (if S = ∅ then 1 - ∑ T, σs T else 0), ?_, ?_, ?_, ?_⟩
    · intro S
      have := hpos S
      show 0 ≤ σs S + (if S = ∅ then 1 - ∑ T, σs T else 0)
      split_ifs <;> linarith
    · intro x
      rw [Finset.sum_add_distrib, hmarg x]
      have : ∑ S ∈ Finset.univ.filter (fun S : Finset α => x ∈ S),
          (if S = ∅ then 1 - ∑ T, σs T else 0) = 0 := by
        refine Finset.sum_eq_zero (fun S hS => ?_)
        simp only [Finset.mem_filter] at hS
        rw [if_neg]
        rintro rfl
        simp at hS
      rw [this, add_zero]
    · intro C hC
      rw [Finset.sum_add_distrib]
      have h0 : ∑ S ∈ Finset.univ.filter (fun S : Finset α => (S ∩ C).Nonempty),
          (if S = ∅ then 1 - ∑ T, σs T else 0) = 0 := by
        refine Finset.sum_eq_zero (fun S hS => ?_)
        simp only [Finset.mem_filter] at hS
        rw [if_neg]
        rintro rfl
        simp at hS
      rw [h0, add_zero]
      exact (hit_iff σs ρ π hmarg C).2 (hcon C hC)
    · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
