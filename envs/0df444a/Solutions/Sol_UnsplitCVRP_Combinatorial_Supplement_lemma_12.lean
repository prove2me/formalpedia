-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.Supplement.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:24.675864+00:00
-- url     : https://prove2.me/submissions/f129494b-7f6c-493d-80f6-3f9f97a9b2e8

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

open UnsplitCVRP
open UnsplitCVRP.Combinatorial
open UnsplitCVRP.Combinatorial.Supplement

/-- Lemma 12, p. 9: under independent rounding with probabilities `min {1, γ x_T}`,
a big client is left uncovered with probability at most `e^{-γ}`. -/
theorem solution {n : ℕ} (d : Fin (n + 1) → ℝ) (δ γ : ℝ) (hγ : 0 ≤ γ)
    (x : List (Fin (n + 1)) → ℝ) (hx : IsConfigFeasible d δ x)
    (v : Fin (n + 1)) (hv : v ∈ bigIn d δ (clients n)) :
    probNotCovered d δ γ x v ≤ Real.exp (-γ) := by
      classical
      set J := configTours d δ with hJ
      set p : List (Fin (n + 1)) → ℝ := fun T => roundProb γ x T with hp
      set Jv := J.filter (fun T => v ∈ T) with hJv
      set K := J.filter (fun T => v ∉ T) with hK
      have hset : J.powerset.filter (fun S => v ∉ covered S) = K.powerset := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, covered, Finset.mem_biUnion,
          List.mem_toFinset, hK, Finset.subset_iff]
        constructor
        · rintro ⟨h1, h2⟩ T hT
          exact ⟨h1 hT, fun hvT => h2 ⟨T, hT, hvT⟩⟩
        · intro h
          exact ⟨fun T hT => (h hT).1, fun ⟨T, hT, hvT⟩ => (h hT).2 hvT⟩
      have hw : ∀ S ∈ K.powerset, sampleWeight d δ γ x S =
          (∏ T ∈ Jv, (1 - p T)) * ((∏ T ∈ S, p T) * ∏ T ∈ K \ S, (1 - p T)) := by
        intro S hS
        rw [Finset.mem_powerset] at hS
        unfold sampleWeight
        rw [← Finset.prod_filter_mul_prod_filter_not (J \ S) (fun T => v ∈ T)]
        have e1 : (J \ S).filter (fun T => v ∈ T) = Jv := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_sdiff, hJv]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            refine ⟨⟨h1, fun hTS => ?_⟩, h3⟩
            have := hS hTS
            rw [hK, Finset.mem_filter] at this
            exact this.2 h3
        have e2 : (J \ S).filter (fun T => ¬ v ∈ T) = K \ S := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_sdiff, hK]
          tauto
        rw [e1, e2]
        ring
      have hsum : probNotCovered d δ γ x v = ∏ T ∈ Jv, (1 - p T) := by
        unfold probNotCovered
        rw [hset, Finset.sum_congr rfl hw, ← Finset.mul_sum, ← Finset.prod_add]
        simp
      have hp1 : ∀ T ∈ J, 0 ≤ 1 - p T := by
        intro T _
        simp only [hp, roundProb]
        linarith [min_le_left (1 : ℝ) (γ * x T)]
      have hp2 : ∀ T ∈ J, 1 - p T ≤ Real.exp (-(γ * x T)) := by
        intro T _
        simp only [hp, roundProb]
        have := Real.add_one_le_exp (-(γ * x T))
        have := min_le_right (1 : ℝ) (γ * x T)
        have := Real.exp_pos (-(γ * x T))
        rcases le_total 1 (γ * x T) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      rw [hsum]
      calc ∏ T ∈ Jv, (1 - p T) ≤ ∏ T ∈ Jv, Real.exp (-(γ * x T)) := by
            apply Finset.prod_le_prod
            · intro T hT; exact hp1 T (Finset.mem_filter.mp hT).1
            · intro T hT; exact hp2 T (Finset.mem_filter.mp hT).1
        _ = Real.exp (-(γ * ∑ T ∈ Jv, x T)) := by
            rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        _ ≤ Real.exp (-γ) := by
            apply Real.exp_le_exp.mpr
            have := hx.2 v hv
            have : γ * 1 ≤ γ * ∑ T ∈ Jv, x T := mul_le_mul_of_nonneg_left this hγ
            linarith
