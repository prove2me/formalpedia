-- Prove2me | solution 1 for ShapleyScarf.TopTrading.section7_core_not_competitive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:51:14.651663+00:00
-- url     : https://prove2.me/submissions/5dc9eee5-3b66-43ba-9bc8-28ae2951d4d4

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market

open ShapleyScarf.TopTrading
set_option maxHeartbeats 0

private theorem competitive_unique (σ : Fin 3 → Fin 3) (price : Fin 3 → ℝ)
    (hc : IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) σ price) :
    σ = ![2, 0, 1] ∧ ∀ k k', price k = price k' := by
  have hi := hc.1.1
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hi h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hi h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hi h)
  have hd := hc.2
  generalize h0 : σ 0 = a
  generalize h1 : σ 1 = b
  generalize h2 : σ 2 = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp +decide [h0, h1, h2] at h01 h02 h12
  all_goals
    simp +decide [Fin.forall_fin_succ, h0, h1, h2] at hd
  all_goals
    obtain ⟨d0, d1, d2⟩ := hd
    try { exfalso; aesop }
  all_goals
    by_cases p01 : price 0 ≤ price 1
    <;> by_cases p02 : price 0 ≤ price 2
    <;> by_cases p10 : price 1 ≤ price 0
    <;> by_cases p12 : price 1 ≤ price 2
    <;> by_cases p20 : price 2 ≤ price 0
    <;> by_cases p21 : price 2 ≤ price 1
    <;> simp_all
    <;> try { exfalso; linarith }
  all_goals
    constructor
    · funext i; fin_cases i <;> simp_all
    · intro k k'; fin_cases k <;> fin_cases k' <;> simp_all <;> linarith

theorem solution :
    IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![2, 0, 1]
        (fun _ => 1) ∧
    (∀ (σ : Fin 3 → Fin 3) (price : Fin 3 → ℝ),
        IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) σ price →
          (fun i => (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) i (σ i))
              = ![2, 1, 1] ∧
            ∀ k k', price k = price k') ∧
      IsCoreAllocation (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![1, 0, 2] ∧
      ¬ ∃ price : Fin 3 → ℝ,
          IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![1, 0, 2]
            price := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · constructor
      · intro i j; fin_cases i <;> fin_cases j <;> simp +decide
      · intro j; fin_cases j
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨0, rfl⟩
    · intro i; fin_cases i <;> norm_num [Fin.forall_fin_succ, Matrix.cons_val]
      change (0 : ℝ) ≤ 2 ∧ 1 ≤ (2 : ℝ) ∧ 2 ≤ (2 : ℝ)
      norm_num
  · intro σ price hc
    obtain ⟨rfl, hp⟩ := competitive_unique σ price hc
    refine ⟨?_, hp⟩
    funext i; fin_cases i <;> rfl
  · constructor
    · constructor
      · intro i j; fin_cases i <;> fin_cases j <;> simp +decide
      · intro j; fin_cases j
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
    · rintro ⟨S, τ, hn, hS, hi, hb⟩
      have n1 : (1 : Fin 3) ∉ S := by
        intro hm
        have h := hb 1 hm
        generalize τ 1 = k at h
        fin_cases k <;> norm_num at h
      have n2 : (2 : Fin 3) ∉ S := by
        intro hm
        have h := hb 2 hm
        change (0 : ℝ) < ![-1, 1, 0] (τ 2) at h
        have ht := hS 2 hm
        generalize he : τ 2 = k at h ht
        fin_cases k <;> norm_num [Matrix.cons_val] at h
        exact n1 ht
      obtain ⟨i, hiS⟩ := hn
      fin_cases i
      · have h := hb 0 hiS
        have ht := hS 0 hiS
        generalize he : τ 0 = k at h ht
        fin_cases k <;> norm_num at h
        exact n2 ht
      · exact n1 hiS
      · exact n2 hiS
  · rintro ⟨price, hc⟩
    have h := (competitive_unique _ price hc).1
    have := congrFun h 0
    exact (by decide : (1 : Fin 3) ≠ 2) this


#print axioms solution
