-- Prove2me | solution 1 for TwoEchelonCVRP.LPCompare.lf_optimal_y
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:16:26.110421+00:00
-- url     : https://prove2.me/submissions/8181928b-b51b-475a-b913-f8580ce27ac9

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

open TwoEchelonCVRP.LPCompare Finset in
theorem solution {I : Instance} (RS : RouteSystem I) (hg : ∀ r, 0 < RS.g r)
    (p : LFPoint RS) (hp : IsOptimalLF p) :
    ∀ r, p.y r = (∑ k ∈ RS.R1 r, p.qd r k) / (I.Q1 : ℝ) := by
  classical
  obtain ⟨hf, hmin⟩ := hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hf
  intro r
  by_contra hne
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ RS.R1 r, p.qd r k := ⟨_, rfl⟩
  rw [← hS] at hne
  have hQ : (0 : ℝ) < I.Q1 := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) I.Q2_lt_Q1
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun k _ => h10 r k
  have hge : S / I.Q1 ≤ p.y r := by
    rw [div_le_iff₀ hQ]; have := h7 r; rw [← hS] at this; linarith
  have hlt : S / I.Q1 < p.y r := lt_of_le_of_ne hge (Ne.symm hne)
  have hy' : ∀ r', Function.update p.y r (S / I.Q1) r' ≤ p.y r' := by
    intro r'
    by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hge
    · exact le_of_eq (Function.update_of_ne h _ _)
  let p' : LFPoint RS := ⟨p.x, Function.update p.y r (S / I.Q1), p.qd⟩
  have feas : IsFeasibleLF p' := by
    refine ⟨h1, h2, h3, h4, le_trans (Finset.sum_le_sum fun r' _ => hy' r') h5, h6, ?_, h8, ?_,
      h10, h11⟩
    · intro r'
      show ∑ k ∈ RS.R1 r', p.qd r' k ≤ (I.Q1 : ℝ) * Function.update p.y r (S / I.Q1) r'
      by_cases h : r' = r
      · subst h
        exact le_of_eq (by rw [Function.update_self, ← hS, mul_div_cancel₀ _ hQ.ne'])
      · rw [Function.update_of_ne h]; exact h7 r'
    · intro r'
      show 0 ≤ Function.update p.y r (S / I.Q1) r' ∧ Function.update p.y r (S / I.Q1) r' ≤ 1
      by_cases h : r' = r
      · subst h
        rw [Function.update_self]
        exact ⟨div_nonneg hS0 hQ.le, le_trans hge (h9 r').2⟩
      · rw [Function.update_of_ne h]; exact h9 r'
  have hc := hmin p' feas
  change ∑ l, RS.c l * p.x l + ∑ r, RS.g r * p.y r ≤
    ∑ l, RS.c l * p.x l + ∑ r', RS.g r' * Function.update p.y r (S / I.Q1) r' at hc
  have hlt' : ∑ r', RS.g r' * Function.update p.y r (S / I.Q1) r' < ∑ r', RS.g r' * p.y r' := by
    refine Finset.sum_lt_sum (fun r' _ => mul_le_mul_of_nonneg_left (hy' r') (hg r').le)
      ⟨r, Finset.mem_univ r, ?_⟩
    rw [Function.update_self]
    exact mul_lt_mul_of_pos_left hlt (hg r)
  linarith
