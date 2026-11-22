-- Prove2me | solution 1 for PauliMixedness.Randomized.levin_work_investment
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:18:56.402896+00:00
-- url     : https://prove2.me/submissions/79306e75-fd34-4479-b6c5-5dd8969aa0d7

import Mathlib

open scoped BigOperators

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : Fin k → ℝ) (μ : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hmean : μ ≤ (∑ x : Fin k, f x) / k) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ ⌈Real.log (k : ℝ) / Real.log 3⌉₊ ∧
      (3 : ℝ) ^ (-(i : ℤ)) / (⌈Real.log (k : ℝ) / Real.log 3⌉₊ : ℝ) ≤
        ((Finset.univ.filter (fun x => (3 : ℝ)^((i : ℤ) - 2) * μ ≤ f x)).card : ℝ) /
          (k : ℝ) := by
  classical
  let L : ℕ := ⌈Real.log (k : ℝ) / Real.log 3⌉₊
  let t : ℕ → ℝ := fun i => (3 : ℝ) ^ ((i : ℤ) - 2) * μ
  let A : ℕ → Finset (Fin k) := fun i => Finset.univ.filter (fun x => t i ≤ f x)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hL1 : 1 ≤ L := Nat.one_le_ceil_iff.mpr (div_pos hlogk hlog3)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have h3L : (k : ℝ) ≤ 3 ^ L := by
    have h1 : Real.log (k : ℝ) / Real.log 3 ≤ (L : ℝ) := Nat.le_ceil _
    have h2 : Real.log (k : ℝ) ≤ (L : ℝ) * Real.log 3 := by
      have h3 := mul_le_mul_of_nonneg_right h1 hlog3.le
      rwa [div_mul_cancel₀ _ hlog3.ne'] at h3
    have h4 : (L : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ L) := by
      rw [Real.log_pow]
    rw [h4] at h2
    exact (Real.log_le_log_iff hkpos (by positivity)).mp h2
  -- monotonicity and positivity of the levels, once `μ > 0`
  have ht_mono : ∀ i j : ℕ, 0 < μ → 1 ≤ i → i ≤ j → t i ≤ t j := by
    intro i j hμ hi hij
    have h3 : (3 : ℝ) ^ ((i : ℤ) - 2) ≤ (3 : ℝ) ^ ((j : ℤ) - 2) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      omega
    exact mul_le_mul_of_nonneg_right h3 hμ.le
  have ht_pos : ∀ i, 0 < μ → 0 < t i := by
    intro i hμ
    have h3 : (0 : ℝ) < (3 : ℝ) ^ ((i : ℤ) - 2) := by positivity
    exact mul_pos h3 hμ
  by_cases hcase : (A L).card = 0
  · -- ## Case B: every `f x < t L`; contradict the mean hypothesis
    by_contra hno
    push_neg at hno
    have hAempty : A L = ∅ := Finset.card_eq_zero.mp hcase
    -- `μ > 0`
    have hμpos : 0 < μ := by
      let x0 : Fin k := ⟨0, by omega⟩
      have hnot : x0 ∉ A L := by rw [hAempty]; simp
      have hlt : f x0 < t L := by
        have : ¬ (t L ≤ f x0) := by simpa [A] using hnot
        exact not_le.mp this
      have hpos : 0 < t L := lt_of_le_of_lt (hf x0) hlt
      have h3 : (0 : ℝ) < (3 : ℝ) ^ ((L : ℤ) - 2) := by positivity
      exact pos_of_mul_pos_right (by simpa [t] using hpos) h3.le
    have hxlt : ∀ x : Fin k, f x < t L := by
      intro x
      have hnot : x ∉ A L := by rw [hAempty]; simp
      have : ¬ (t L ≤ f x) := by simpa [A] using hnot
      exact not_le.mp this
    -- pointwise layer-cake bound
    have hpoint : ∀ x : Fin k,
        f x ≤ t 1 + ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * (if t i ≤ f x then (1 : ℝ) else 0) := by
      intro x
      by_cases hsmall : f x < t 1
      · have hsum0 : (∑ i ∈ Finset.Icc 1 (L - 1),
            t (i + 1) * (if t i ≤ f x then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hti : t 1 ≤ t i := ht_mono 1 i hμpos le_rfl hi1
          have hfalse : ¬ (t i ≤ f x) := not_le.mpr (lt_of_lt_of_le hsmall hti)
          simp [hfalse]
        rw [hsum0, add_zero]
        linarith
      · push_neg at hsmall
        have hL2 : 2 ≤ L := by
          by_contra h
          push_neg at h
          have hL1' : L = 1 := by omega
          have ht : t L = t 1 := by rw [hL1']
          linarith [hxlt x]
        let S : Finset ℕ := (Finset.Icc 1 (L - 1)).filter (fun i => t i ≤ f x)
        have h1S : 1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨le_rfl, by omega⟩, hsmall⟩
        have hSne : S.Nonempty := ⟨1, h1S⟩
        let j : ℕ := S.max' hSne
        have hjS : j ∈ S := Finset.max'_mem S hSne
        have hjIcc : j ∈ Finset.Icc 1 (L - 1) := (Finset.mem_filter.mp hjS).1
        have hjle : j ≤ L - 1 := (Finset.mem_Icc.mp hjIcc).2
        have hflt : f x < t (j + 1) := by
          rcases lt_or_eq_of_le hjle with hlt | heq
          · have hmem : j + 1 ∈ Finset.Icc 1 (L - 1) := by
              simp only [Finset.mem_Icc]; omega
            by_contra hcon
            push_neg at hcon
            have hmemS : j + 1 ∈ S := by
              simp only [S, Finset.mem_filter]; exact ⟨hmem, hcon⟩
            have hle : j + 1 ≤ j := Finset.le_max' S (j + 1) hmemS
            omega
          · have hjeq : j + 1 = L := by omega
            rw [hjeq]
            exact hxlt x
        have hterm : t (j + 1) ≤ ∑ i ∈ S, t (i + 1) := by
          exact Finset.single_le_sum (s := S) (f := fun i => t (i + 1))
            (fun i _ => (ht_pos (i + 1) hμpos).le) hjS
        have hSsum : (∑ i ∈ S, t (i + 1)) =
            ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * (if t i ≤ f x then (1 : ℝ) else 0) := by
          have hSdef : S = (Finset.Icc 1 (L - 1)).filter (fun i => t i ≤ f x) := rfl
          rw [hSdef, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : t i ≤ f x <;> simp [h]
        rw [← hSsum]
        exact le_trans (le_trans hflt.le hterm) (le_add_of_nonneg_left (ht_pos 1 hμpos).le)
    -- sum the pointwise bound
    have hsum1 : (∑ x : Fin k, f x) ≤
        (k : ℝ) * t 1 + ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((A i).card : ℝ) := by
      calc (∑ x : Fin k, f x) ≤
          ∑ x : Fin k, (t 1 + ∑ i ∈ Finset.Icc 1 (L - 1),
            t (i + 1) * (if t i ≤ f x then (1 : ℝ) else 0)) :=
            Finset.sum_le_sum (fun x _ => hpoint x)
        _ = (k : ℝ) * t 1 + ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((A i).card : ℝ) := by
            rw [Finset.sum_add_distrib]
            have hc : (∑ _x : Fin k, t 1) = (k : ℝ) * t 1 := by
              rw [Finset.sum_const, Finset.card_univ]
              simp
            rw [hc]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_boole]
    -- bound each term using the negated goal
    have hle_term : ∀ i ∈ Finset.Icc 1 (L - 1),
        t (i + 1) * ((A i).card : ℝ) ≤ t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ)) := by
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hiL : i ≤ L := by have := (Finset.mem_Icc.mp hi).2; omega
      have hlt := hno i hi1 hiL
      have hnle : ((A i).card : ℝ) ≤ (k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hlt.le hkpos.le
        rw [div_mul_cancel₀ _ hkpos.ne'] at h
        calc ((A i).card : ℝ) ≤ (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ) * (k : ℝ) := h
          _ = (k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ) := by ring
      exact mul_le_mul_of_nonneg_left hnle (ht_pos (i + 1) hμpos).le
    have hsum2 : (∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((A i).card : ℝ)) ≤
        ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ)) :=
      Finset.sum_le_sum hle_term
    -- compute the geometric sum
    have hterm_eq : ∀ i : ℕ, t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ)) =
        (k : ℝ) * μ / (3 * (L : ℝ)) := by
      intro i
      have h3 : (3 : ℝ) ^ (((i : ℤ) + 1) - 2) * (3 : ℝ) ^ (-(i : ℤ)) = 1 / 3 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        have hexp : ((i : ℤ) + 1 - 2) + (-(i : ℤ)) = -1 := by ring
        rw [hexp, zpow_neg, zpow_one]
        norm_num
      have ht : t (i + 1) = (3 : ℝ) ^ (((i : ℤ) + 1) - 2) * μ := rfl
      rw [ht]
      linear_combination (μ * k / (L : ℝ)) * h3
    have hterm_sum : (∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ))) =
        ∑ _i ∈ Finset.Icc 1 (L - 1), ((k : ℝ) * μ / (3 * (L : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm_eq i
    have hcard : (Finset.Icc 1 (L - 1)).card = L - 1 := by
      rw [Nat.card_Icc]
      omega
    have hcalc : (∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ))) =
        ((L : ℝ) - 1) * ((k : ℝ) * μ / (3 * (L : ℝ))) := by
      rw [hterm_sum, Finset.sum_const, hcard, nsmul_eq_mul]
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub hL1]
        ring
      rw [hcast]
    -- final arithmetic
    have hmean' : (k : ℝ) * μ ≤ ∑ x : Fin k, f x := by
      have h := mul_le_mul_of_nonneg_right hmean hkpos.le
      rw [div_mul_cancel₀ _ hkpos.ne'] at h
      simpa [mul_comm] using h
    have ht1 : t 1 = μ / 3 := by
      show (3 : ℝ) ^ (((1 : ℕ) : ℤ) - 2) * μ = μ / 3
      norm_num
      ring
    have hstep : (k : ℝ) * t 1 + ((L : ℝ) - 1) * ((k : ℝ) * μ / (3 * (L : ℝ))) =
        (k : ℝ) * μ * ((2 * (L : ℝ) - 1) / (3 * (L : ℝ))) := by
      rw [ht1]
      have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
      field_simp
      ring
    have hratio : (2 * (L : ℝ) - 1) / (3 * (L : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hkμ : 0 < (k : ℝ) * μ := mul_pos hkpos hμpos
    have hstrict : (∑ x : Fin k, f x) < (k : ℝ) * μ := by
      calc (∑ x : Fin k, f x) ≤ (k : ℝ) * t 1 + ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((A i).card : ℝ) := hsum1
        _ ≤ (k : ℝ) * t 1 + ∑ i ∈ Finset.Icc 1 (L - 1), t (i + 1) * ((k : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) / (L : ℝ)) := by
            linarith
        _ = (k : ℝ) * t 1 + ((L : ℝ) - 1) * ((k : ℝ) * μ / (3 * (L : ℝ))) := by rw [hcalc]
        _ = (k : ℝ) * μ * ((2 * (L : ℝ) - 1) / (3 * (L : ℝ))) := hstep
        _ < (k : ℝ) * μ * 1 := by
            exact mul_lt_mul_of_pos_left hratio hkμ
        _ = (k : ℝ) * μ := by ring
    linarith
  · -- ## Case A: `A L` is nonempty, take `i = L`
    refine ⟨L, hL1, le_rfl, ?_⟩
    change (3 : ℝ) ^ (-(L : ℤ)) / (L : ℝ) ≤ ((A L).card : ℝ) / (k : ℝ)
    have hAn : 1 ≤ (A L).card := Nat.one_le_iff_ne_zero.mpr hcase
    have hnR : (1 : ℝ) ≤ ((A L).card : ℝ) := by exact_mod_cast hAn
    have h3neg_eq : (3 : ℝ) ^ (-(L : ℤ)) = 1 / (3 : ℝ) ^ L := by
      rw [zpow_neg, zpow_natCast, one_div]
    have h3neg_le : (3 : ℝ) ^ (-(L : ℤ)) ≤ 1 / (k : ℝ) := by
      rw [h3neg_eq]
      exact one_div_le_one_div_of_le hkpos h3L
    have hdiv1 : (3 : ℝ) ^ (-(L : ℤ)) / (L : ℝ) ≤ 1 / (k : ℝ) := by
      have h3nn : 0 ≤ (3 : ℝ) ^ (-(L : ℤ)) := by positivity
      have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
      have hdiv : (3 : ℝ) ^ (-(L : ℤ)) / (L : ℝ) ≤ (3 : ℝ) ^ (-(L : ℤ)) := by
        rw [div_le_iff₀ hLpos]
        calc (3 : ℝ) ^ (-(L : ℤ)) = (3 : ℝ) ^ (-(L : ℤ)) * 1 := by ring
          _ ≤ (3 : ℝ) ^ (-(L : ℤ)) * (L : ℝ) := mul_le_mul_of_nonneg_left hL1R h3nn
      linarith
    have hdiv2 : (1 : ℝ) / (k : ℝ) ≤ ((A L).card : ℝ) / (k : ℝ) := by
      apply div_le_div_of_nonneg_right hnR hkpos.le
    linarith

