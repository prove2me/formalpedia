-- Prove2me | solution 1 for ResolvingNRM.FRUpper.sqrt_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:17.998168+00:00
-- url     : https://prove2.me/submissions/a949e02a-2dd9-486f-8097-a7522cdec743

import Mathlib

set_option autoImplicit false

lemma HH_inv_sqrt_sum (N : ℕ) : ∑ k ∈ Finset.range N, 1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have key : 1 / Real.sqrt ((N : ℝ) + 1) ≤ 2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ)) := by
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ))]
    push_cast
    linarith

lemma HH_tail (T' : ℕ) (hT : 0 < T') (t : ℕ) (ht : t < T') :
    ∑ i ∈ Finset.range t, 1 / ((T' : ℝ) - i) ^ 2 ≤ 1 / ((T' : ℝ) - t) := by
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, sub_zero]
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  | succ t ih =>
    have ih := ih (by omega)
    rw [Finset.sum_range_succ]
    have hx : (2 : ℝ) ≤ (T' : ℝ) - t := by
      have : t + 2 ≤ T' := by omega
      have : ((t : ℝ) + 2) ≤ T' := by exact_mod_cast this
      linarith
    set x : ℝ := (T' : ℝ) - t with hxdef
    have hx1 : (T' : ℝ) - ((t + 1 : ℕ) : ℝ) = x - 1 := by push_cast; rw [hxdef]; ring
    rw [hx1]
    have h1 : 1 / x + 1 / x ^ 2 ≤ 1 / (x - 1) := by
      have hx0 : 0 < x := by linarith
      have hx1' : 0 < x - 1 := by linarith
      rw [div_add_div _ _ hx0.ne' (by positivity), div_le_div_iff₀ (by positivity) hx1']
      nlinarith
    linarith

theorem solution (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2)
      ≤ 2 * Real.sqrt T + Real.sqrt 2 := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hc : ∀ i : ℕ, ((T' + 1 : ℕ) : ℝ) - i - 1 = (T' : ℝ) - i := by
    intro i; push_cast; ring
  simp_rw [hc]
  rw [Finset.sum_range_succ]
  have hlast : Real.sqrt (∑ i ∈ Finset.range T', 1 / ((T' : ℝ) - i) ^ 2) ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    rcases Nat.eq_zero_or_pos T' with h0 | hpos
    · subst h0; simp
    · obtain ⟨s, rfl⟩ : ∃ s, T' = s + 1 := ⟨T' - 1, by omega⟩
      rw [Finset.sum_range_succ]
      have h1 := HH_tail (s + 1) (by omega) s (by omega)
      have h2 : ((s + 1 : ℕ) : ℝ) - s = 1 := by push_cast; ring
      rw [h2] at h1 ⊢
      norm_num at h1 ⊢
      linarith
  have hmain : ∑ t ∈ Finset.range T', Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T' : ℝ) - i) ^ 2)
      ≤ 2 * Real.sqrt T' := by
    rcases Nat.eq_zero_or_pos T' with h0 | hpos
    · subst h0; simp
    calc ∑ t ∈ Finset.range T', Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T' : ℝ) - i) ^ 2)
        ≤ ∑ t ∈ Finset.range T', 1 / Real.sqrt ((T' : ℝ) - t) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          have htt := HH_tail T' hpos t (Finset.mem_range.mp ht)
          have hp' : (0:ℝ) ≤ (T' : ℝ) - t := by
            have : (t:ℝ) < T' := by exact_mod_cast Finset.mem_range.mp ht
            linarith
          calc Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T' : ℝ) - i) ^ 2)
              ≤ Real.sqrt (1 / ((T' : ℝ) - t)) := Real.sqrt_le_sqrt htt
            _ = 1 / Real.sqrt ((T' : ℝ) - t) := by rw [Real.sqrt_div' _ hp']; simp
      _ = ∑ k ∈ Finset.range T', 1 / Real.sqrt ((k : ℝ) + 1) := by
          rw [← Finset.sum_range_reflect (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1)) T']
          refine Finset.sum_congr rfl (fun t ht => ?_)
          have htt := Finset.mem_range.mp ht
          have h : ((T' - 1 - t : ℕ) : ℝ) + 1 = (T' : ℝ) - t := by
            have e : ((T' - 1 - t : ℕ) : ℝ) = (T' : ℝ) - 1 - t := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
            rw [e]; ring
          simp only [h]
      _ ≤ 2 * Real.sqrt T' := HH_inv_sqrt_sum T'
  have hmono : Real.sqrt (T' : ℝ) ≤ Real.sqrt ((T' + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  linarith
