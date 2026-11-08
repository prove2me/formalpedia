-- Prove2me | solution 1 for PCLAssort.observation_1_g_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:43:55.762853+00:00
-- url     : https://prove2.me/submissions/0ef17e58-0302-4d77-ad1b-fa5c67537a5b

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_gValue

namespace Aux_PCL_g_anti
open PCLAssort

theorem coef_nonneg (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ^ (1 / γ) / (a ^ (1 / γ) + b ^ (1 / γ)) ^ (1 - γ) :=
  div_nonneg (Real.rpow_nonneg ha _)
    (Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)) _)

theorem coef_le (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    a ^ (1 / γ) / (a ^ (1 / γ) + b ^ (1 / γ)) ^ (1 - γ) ≤ a := by
  set A := a ^ (1 / γ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg ha _
  have hB0 : 0 ≤ b ^ (1 / γ) := Real.rpow_nonneg hb _
  rcases hA0.eq_or_lt with h | h
  · rw [← h, zero_div]; exact ha
  · have h1 : A ^ (1 - γ) ≤ (A + b ^ (1 / γ)) ^ (1 - γ) :=
      Real.rpow_le_rpow hA0 (by linarith) (by linarith)
    have h2 : 0 < A ^ (1 - γ) := Real.rpow_pos_of_pos h _
    calc A / (A + b ^ (1 / γ)) ^ (1 - γ) ≤ A / A ^ (1 - γ) :=
          div_le_div_of_nonneg_left hA0 h2 h1
      _ = A ^ γ := by
          rw [div_eq_iff h2.ne', ← Real.rpow_add h, show γ + (1 - γ) = (1 : ℝ) by ring,
            Real.rpow_one]
      _ = a := by
          rw [hA, ← Real.rpow_mul ha, one_div, inv_mul_cancel₀ hγ0.ne', Real.rpow_one]

theorem xi_eq {n : ℕ} (I : PCLInstance n) (z : ℝ) (k l p : Fin n) :
    xiShare I z k l p = (I.r p - z) * (I.v p ^ (1 / I.γ k l) /
      (I.v k ^ (1 / I.γ k l) + I.v l ^ (1 / I.γ k l)) ^ (1 - I.γ k l)) := by
  unfold xiShare; rw [mul_div_assoc]

theorem xi_mono {n : ℕ} (I : PCLInstance n) {z1 z2 : ℝ} (hz : z1 ≤ z2) (k l p : Fin n)
    (hp : p = k ∨ p = l) :
    xiShare I z2 k l p ≤ xiShare I z1 k l p := by
  rw [xi_eq, xi_eq]
  apply mul_le_mul_of_nonneg_right (by linarith)
  apply div_nonneg (Real.rpow_nonneg (I.v_nonneg p) _)
  exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (I.v_nonneg k) _)
    (Real.rpow_nonneg (I.v_nonneg l) _)) _

theorem weight_anti {n : ℕ} (I : PCLInstance n) {z1 z2 : ℝ} (hz : z1 ≤ z2)
    (e : Option (Fin n) × Option (Fin n)) :
    pclWeight I z2 e ≤ pclWeight I z1 e := by
  rcases e with ⟨_ | i, _ | j⟩
  · simp [pclWeight]
  · simp [pclWeight]
  · simp only [pclWeight]
    apply Finset.sum_le_sum
    intro k _
    exact add_le_add (xi_mono I hz i k i (Or.inl rfl)) (xi_mono I hz k i i (Or.inr rfl))
  · simp only [pclWeight]
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg hij, xi_eq, xi_eq, xi_eq, xi_eq]
      have hC1 := coef_le (I.v i) (I.v j) (I.γ i j) (I.v_nonneg i) (I.v_nonneg j)
        (I.γ_pos i j hij) (I.γ_le_one i j hij)
      have hC2 := coef_le (I.v i) (I.v j) (I.γ j i) (I.v_nonneg i) (I.v_nonneg j)
        (I.γ_pos j i (Ne.symm hij)) (I.γ_le_one j i (Ne.symm hij))
      rw [add_comm (I.v i ^ (1 / I.γ j i))] at hC2
      set C1 := I.v i ^ (1 / I.γ i j) / (I.v i ^ (1 / I.γ i j) + I.v j ^ (1 / I.γ i j)) ^ (1 - I.γ i j)
      set C2 := I.v i ^ (1 / I.γ j i) / (I.v j ^ (1 / I.γ j i) + I.v i ^ (1 / I.γ j i)) ^ (1 - I.γ j i)
      have hK : 0 ≤ 2 * I.v i - C1 - C2 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hz) hK]

end Aux_PCL_g_anti

open PCLAssort Aux_PCL_g_anti in
theorem solution {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (c : ℝ) (hc : 0 ≤ c) :
    Antitone (fun z => gValue I s c z) := by
  intro z1 z2 hz
  simp only
  unfold gValue
  have hne : (LPzFeasible n s c).Nonempty := ⟨(fun _ => 0, fun _ => 0), by simp [LPzFeasible, hc]⟩
  have hbdd : BddAbove ((fun p => LP9Objective (pclEdges n) (pclWeight I z1) p) ''
      LPzFeasible n s c) := by
    refine ⟨∑ e ∈ pclEdges n, |pclWeight I z1 e|, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    unfold LP9Objective
    apply Finset.sum_le_sum
    intro e he
    have h0 := hp.2.2.2.2.2.2.1 e he
    have hne1 : e.1 ≠ none := (Finset.mem_filter.mp he).2.1
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne1
    have h1 : p.2 e ≤ 1 := (hp.1 e he).trans (by rw [hi]; exact hp.2.2.1 i)
    calc pclWeight I z1 e * p.2 e ≤ |pclWeight I z1 e| * p.2 e :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |pclWeight I z1 e| := by nlinarith [abs_nonneg (pclWeight I z1 e)]
  apply csSup_le (hne.image _)
  rintro _ ⟨p, hp, rfl⟩
  refine le_trans ?_ (le_csSup hbdd ⟨p, hp, rfl⟩)
  unfold LP9Objective
  apply Finset.sum_le_sum
  intro e he
  exact mul_le_mul_of_nonneg_right (weight_anti I hz e) (hp.2.2.2.2.2.2.1 e he)
