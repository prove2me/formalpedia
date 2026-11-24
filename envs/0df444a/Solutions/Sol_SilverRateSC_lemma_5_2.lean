-- Prove2me | solution 1 for SilverRateSC.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:11:12.834723+00:00
-- url     : https://prove2.me/submissions/f1772f4d-f441-486a-aa7a-3de57954eccc

import Mathlib

namespace SolSilverRateFiveTwo

open Finset

/-- Tangent-line bound for the logarithm at `a > 0`. -/
theorem log_le_tangent (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
    Real.log y ≤ Real.log a + y / a - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y / a by positivity)
  rw [Real.log_div hy.ne' ha.ne'] at h
  linarith

/-- Split an `Icc` sum at an interior point. -/
theorem sum_Icc_split (h : ℕ → ℝ) (a b c : ℕ) (hab : a ≤ b + 1) (hbc : b ≤ c) :
    ∑ t ∈ Icc a c, h t = ∑ t ∈ Icc a b, h t + ∑ t ∈ Icc (b + 1) c, h t := by
  rw [← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc,
    sum_Ico_consecutive _ hab (by omega)]

end SolSilverRateFiveTwo

open SolSilverRateFiveTwo in
theorem solution (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (h : ℕ → ℝ)
    (hh : ∀ t ∈ Finset.Icc 1 n, 0 ≤ h t) (S₀ : ℝ) (hS₀ : 0 < S₀) (J : ℕ)
    (hJ : J ≤ ⌈(n : ℝ) / m⌉₊) (u p v : ℕ → ℕ)
    (huv : ∀ j ∈ Finset.Icc 1 J, 1 ≤ u j ∧ u j ≤ p j ∧ p j ≤ v j ∧ v j ≤ n)
    (hup : ∀ j ∈ Finset.Icc 1 J, j < J → p j + 1 ≤ u (j + 1))
    (h23 : ∀ j ∈ Finset.Icc 1 J,
      S₀ ≤ ∑ t ∈ Finset.Icc (u j) (v j), h t ∧ ∑ t ∈ Finset.Icc (p j + 1) (v j), h t ≤ S₀ / 4) :
    (∀ t : ℕ, ((Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j)).card ≤ 2) ∧
      ∑ j ∈ Finset.Icc 1 J, (v j - u j + 1) ≤ 2 * n ∧
      ∑ j ∈ Finset.Icc 1 J, Real.log (((v j - u j + 1 : ℕ) : ℝ) + 1) ≤
        (⌈(n : ℝ) / m⌉₊ : ℝ) * Real.log (2 * m + 1) := by
  -- monotonicity of the windows
  have hmono : ∀ d j, 1 ≤ j → j + d + 1 ≤ J → p j + 1 ≤ u (j + d + 1) := by
    intro d
    induction d with
    | zero =>
      intro j h1 h2
      exact hup j (Finset.mem_Icc.2 ⟨h1, by omega⟩) (by omega)
    | succ d ih =>
      intro j h1 h2
      have a := ih j h1 (by omega)
      have b := (huv (j + d + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2.1
      have c := hup (j + d + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (by omega)
      rw [show j + (d + 1) + 1 = j + d + 1 + 1 by omega]
      omega
  have hlt : ∀ j j', 1 ≤ j → j < j' → j' ≤ J → p j + 1 ≤ u j' := by
    intro j j' h1 h2 h3
    have := hmono (j' - j - 1) j h1 (by omega)
    rwa [show j + (j' - j - 1) + 1 = j' by omega] at this
  -- no index lies in three windows
  have key : ∀ t a b c, a < b → b < c →
      a ∈ (Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j) →
      b ∈ (Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j) →
      c ∈ (Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j) → False := by
    intro t a b c hab hbc ha hb hc
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb hc
    have hb' : b ∈ Finset.Icc 1 J := Finset.mem_Icc.2 hb.1
    have hua := huv a (Finset.mem_Icc.2 ha.1)
    have hub := huv b hb'
    have h1 := hlt a b ha.1.1 hab hb.1.2
    have h2 := hlt b c hb.1.1 hbc hc.1.2
    obtain ⟨hS, hsmall⟩ := h23 b hb'
    have hsa := (h23 a (Finset.mem_Icc.2 ha.1)).2
    rw [sum_Icc_split h (u b) (p b) (v b) (by omega) hub.2.2.1] at hS
    have hsub : ∑ x ∈ Finset.Icc (u b) (p b), h x ≤ ∑ x ∈ Finset.Icc (p a + 1) (v a), h x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx _
        rw [Finset.mem_Icc] at hx
        exact hh x (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    linarith
  have part1 : ∀ t : ℕ, ((Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j)).card ≤ 2 := by
    intro t
    by_contra hcon
    rw [not_le, Finset.two_lt_card] at hcon
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hcon
    rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;>
      rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
      rcases Nat.lt_or_gt_of_ne hbc with h3 | h3
    all_goals first
      | exact key t a b c (by omega) (by omega) ha hb hc
      | exact key t a c b (by omega) (by omega) ha hc hb
      | exact key t b a c (by omega) (by omega) hb ha hc
      | exact key t b c a (by omega) (by omega) hb hc ha
      | exact key t c a b (by omega) (by omega) hc ha hb
      | exact key t c b a (by omega) (by omega) hc hb ha
  have part2 : ∑ j ∈ Finset.Icc 1 J, (v j - u j + 1) ≤ 2 * n := by
    have hcard : ∀ j ∈ Finset.Icc 1 J, v j - u j + 1 =
        ∑ t ∈ Finset.Icc 1 n, (if u j ≤ t ∧ t ≤ v j then 1 else 0) := by
      intro j hj
      have hj' := huv j hj
      rw [← Finset.card_filter]
      have : (Finset.Icc 1 n).filter (fun t => u j ≤ t ∧ t ≤ v j) = Finset.Icc (u j) (v j) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [this, Nat.card_Icc]; omega
    rw [Finset.sum_congr rfl hcard, Finset.sum_comm]
    calc ∑ t ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 J, (if u j ≤ t ∧ t ≤ v j then 1 else 0)
        = ∑ t ∈ Finset.Icc 1 n,
            ((Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j)).card := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
      _ ≤ ∑ t ∈ Finset.Icc 1 n, 2 := Finset.sum_le_sum fun t _ => part1 t
      _ = 2 * n := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; omega
  refine ⟨part1, part2, ?_⟩
  -- part 3
  set B : ℕ := ⌈(n : ℝ) / m⌉₊ with hBdef
  set a : ℝ := 2 * (m:ℝ) + 1 with hadef
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hapos : 0 < a := by positivity
  have hnB : (n:ℝ) ≤ m * B := by
    have := Nat.le_ceil ((n:ℝ) / m)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  set X : ℝ := ∑ j ∈ Finset.Icc 1 J, (((v j - u j + 1 : ℕ)) : ℝ) with hXdef
  have hX : X ≤ 2 * n := by
    rw [hXdef]; exact_mod_cast part2
  have hterm : ∀ j ∈ Finset.Icc 1 J, Real.log (((v j - u j + 1 : ℕ) : ℝ) + 1) ≤
      Real.log a + ((((v j - u j + 1 : ℕ) : ℝ) + 1) / a) - 1 :=
    fun j _ => log_le_tangent a _ hapos (by positivity)
  have hsum := Finset.sum_le_sum hterm
  have hrhs : ∑ j ∈ Finset.Icc 1 J, (Real.log a + ((((v j - u j + 1 : ℕ) : ℝ) + 1) / a) - 1)
      = J * Real.log a + (X + J) / a - J := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_add_distrib]
    simp [hXdef]
  rw [hrhs] at hsum
  have hlog : 2 * (m:ℝ) / a ≤ Real.log a := by
    have := Real.one_sub_inv_le_log_of_pos hapos
    have e : 1 - a⁻¹ = 2 * (m:ℝ) / a := by rw [hadef]; field_simp; ring
    linarith
  have hJB : (J:ℝ) ≤ B := by exact_mod_cast hJ
  have h1 : ((B:ℝ) - J) * (2 * (m:ℝ) / a) ≤ ((B:ℝ) - J) * Real.log a :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have h2 : (X + J) / a - J = (X - 2 * m * J) / a := by
    rw [hadef]; field_simp; ring
  have h3 : ((B:ℝ) - J) * (2 * (m:ℝ) / a) = (2 * m * B - 2 * m * J) / a := by ring
  have h4 : (X - 2 * m * J) / a ≤ (2 * m * B - 2 * m * J) / a :=
    div_le_div_of_nonneg_right (by linarith) hapos.le
  linarith
