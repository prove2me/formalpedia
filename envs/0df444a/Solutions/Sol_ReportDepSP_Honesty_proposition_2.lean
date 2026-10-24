-- Prove2me | solution 1 for ReportDepSP.Honesty.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T14:13:38.893305+00:00
-- url     : https://prove2.me/submissions/5b78a938-4099-4a73-ad83-a79d4fe8b12a

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

set_option autoImplicit false

namespace ReportDepSPHonestyAux

open Finset ReportDepSP.Honesty

/-- The first index where a Boolean predicate holds is the minimum of its true set. -/
theorem first_iff {n : ℕ} (p : Fin n → Bool) (h : (univ.filter (fun r => p r = true)).Nonempty)
    (r : Fin n) :
    (p r = true ∧ ∀ t : Fin n, t < r → p t = false) ↔
      r = (univ.filter (fun r => p r = true)).min' h := by
  constructor
  · rintro ⟨hr, hlt⟩
    apply le_antisymm
    · by_contra hc
      push_neg at hc
      have hm := (univ.filter (fun r => p r = true)).min'_mem h
      rw [mem_filter] at hm
      have := hlt _ hc
      rw [hm.2] at this
      exact Bool.noConfusion this
    · exact min'_le _ _ (by simp [hr])
  · rintro rfl
    have hm := (univ.filter (fun r => p r = true)).min'_mem h
    rw [mem_filter] at hm
    refine ⟨hm.2, fun t ht => ?_⟩
    by_contra hc
    have hc' : p t = true := by simpa using hc
    have := min'_le (univ.filter (fun r => p r = true)) t (by simp [hc'])
    exact absurd ht (not_lt.mpr this)

/-- Summing a "first true index" indicator over a down-closed set. -/
theorem sum_first_downset {n : ℕ} (p : Fin n → Bool) (x : ℝ) (s : Finset (Fin n))
    (hs : ∀ r ∈ s, ∀ t : Fin n, t < r → t ∈ s) :
    (∑ r ∈ s, if p r = true ∧ ∀ t : Fin n, t < r → p t = false then x else 0) =
      if ∃ t ∈ s, p t = true then x else 0 := by
  by_cases hex : ∃ t ∈ s, p t = true
  · rw [if_pos hex]
    obtain ⟨t, hts, ht⟩ := hex
    have hne : (univ.filter (fun r => p r = true)).Nonempty := ⟨t, by simp [ht]⟩
    set m := (univ.filter (fun r => p r = true)).min' hne with hmdef
    have hmt : m ≤ t := min'_le _ _ (by simp [ht])
    have hms : m ∈ s := by
      rcases hmt.lt_or_eq with h | h
      · exact hs t hts m h
      · rw [h]; exact hts
    rw [sum_eq_single_of_mem m hms]
    · rw [if_pos ((first_iff p hne m).2 rfl)]
    · intro b _ hb
      rw [if_neg]
      intro hc
      exact hb ((first_iff p hne b).1 hc)
  · rw [if_neg hex]
    apply sum_eq_zero
    intro r hr
    rw [if_neg]
    intro hc
    exact hex ⟨r, hr, hc.1⟩

/-- Cumulative match probability. -/
theorem cum_matchProb {n : ℕ} (P : (Fin n → Bool) → ℝ) (R : Equiv.Perm (Fin n)) (k : Fin n) :
    ∑ r ∈ Iic k, matchProb P R r =
      ∑ a : Fin n → Bool, if ∃ t ∈ Iic k, a (R.symm t) = true then P a else 0 := by
  unfold matchProb
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  exact sum_first_downset (fun r => a (R.symm r)) (P a) (Iic k)
    (fun r hr t ht => by
      rw [mem_Iic] at hr ⊢
      exact ht.le.trans hr)

/-- Total match probability does not depend on the ROL. -/
theorem tot_matchProb {n : ℕ} (P : (Fin n → Bool) → ℝ) (R : Equiv.Perm (Fin n)) :
    ∑ r, matchProb P R r =
      ∑ a : Fin n → Bool, if ∃ s, a s = true then P a else 0 := by
  unfold matchProb
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_first_downset (fun r => a (R.symm r)) (P a) univ (fun _ _ t _ => mem_univ t)]
  by_cases h : ∃ s, a s = true
  · rw [if_pos h, if_pos]
    obtain ⟨s, hs⟩ := h
    exact ⟨R s, mem_univ _, by simpa using hs⟩
  · rw [if_neg h, if_neg]
    rintro ⟨t, _, ht⟩
    exact h ⟨_, ht⟩

theorem one_symm_apply' {n : ℕ} (r : Fin n) : (1 : Equiv.Perm (Fin n)).symm r = r := rfl

/-- The v-part: the truth gives the best attainable option in every state. -/
theorem vpart_le {n : ℕ} (P : (Fin n → Bool) → ℝ) (hP : IsAttainabilityDist P)
    (v : Fin n → ℝ) (hv : Antitone v) (R : Equiv.Perm (Fin n)) :
    ∑ r, matchProb P R r * v (R.symm r) ≤ ∑ r, matchProb P 1 r * v ((1 : Equiv.Perm (Fin n)).symm r) := by
  unfold matchProb
  simp only [sum_mul]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_le_sum
  intro a _
  by_cases h : ∃ s, a s = true
  · obtain ⟨s, hs⟩ := h
    have hR : (univ.filter (fun r => a (R.symm r) = true)).Nonempty := ⟨R s, by simp [hs]⟩
    have h1 : (univ.filter (fun r => a ((1 : Equiv.Perm (Fin n)).symm r) = true)).Nonempty :=
      ⟨s, mem_filter.mpr ⟨mem_univ _, hs⟩⟩
    set mR := (univ.filter (fun r => a (R.symm r) = true)).min' hR
    set m1 := (univ.filter (fun r => a ((1 : Equiv.Perm (Fin n)).symm r) = true)).min' h1
    have eR : (∑ r, (if a (R.symm r) = true ∧ ∀ t : Fin n, t < r → a (R.symm t) = false
        then P a else 0) * v (R.symm r)) = P a * v (R.symm mR) := by
      rw [sum_eq_single_of_mem mR (mem_univ _)]
      · rw [if_pos ((first_iff (fun r => a (R.symm r)) hR mR).2 rfl)]
      · intro b _ hb
        rw [if_neg, zero_mul]
        intro hc
        exact hb ((first_iff (fun r => a (R.symm r)) hR b).1 hc)
    have e1 : (∑ r, (if a ((1 : Equiv.Perm (Fin n)).symm r) = true ∧ ∀ t : Fin n, t < r →
        a ((1 : Equiv.Perm (Fin n)).symm t) = false then P a else 0) *
          v ((1 : Equiv.Perm (Fin n)).symm r)) = P a * v ((1 : Equiv.Perm (Fin n)).symm m1) := by
      rw [sum_eq_single_of_mem m1 (mem_univ _)]
      · rw [if_pos ((first_iff (fun r => a ((1 : Equiv.Perm (Fin n)).symm r)) h1 m1).2 rfl)]
      · intro b _ hb
        rw [if_neg, zero_mul]
        intro hc
        exact hb ((first_iff (fun r => a ((1 : Equiv.Perm (Fin n)).symm r)) h1 b).1 hc)
    rw [eR, e1]
    apply mul_le_mul_of_nonneg_left _ (hP.1 a)
    apply hv
    have hmem := (univ.filter (fun r => a (R.symm r) = true)).min'_mem hR
    rw [mem_filter] at hmem
    have : m1 ≤ R.symm mR :=
      min'_le (univ.filter (fun r => a ((1 : Equiv.Perm (Fin n)).symm r) = true)) (R.symm mR)
        (mem_filter.mpr ⟨mem_univ _, hmem.2⟩)
    rw [one_symm_apply']
    exact this
  · push_neg at h
    apply le_of_eq
    rw [sum_eq_zero, sum_eq_zero]
    · intro r _
      rw [if_neg, zero_mul]
      intro hc
      exact absurd hc.1 (by simp [h])
    · intro r _
      rw [if_neg, zero_mul]
      intro hc
      exact absurd hc.1 (by simp [h])

/-- Iic sums on `Fin n` are range sums of the zero-extension. -/
theorem iic_sum_eq {n : ℕ} (D : Fin n → ℝ) (k : Fin n) :
    ∑ r ∈ Iic k, D r = ∑ j ∈ range ((k : ℕ) + 1), (if h : j < n then D ⟨j, h⟩ else 0) := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, sum_map]
  apply sum_congr rfl
  intro r _
  simp [r.isLt]

/-- Abel summation: nonnegative partial sums, zero total, antitone weights. -/
theorem abel_nonneg {n : ℕ} (D ρ : Fin n → ℝ) (hρ : Antitone ρ)
    (hS : ∀ k : Fin n, 0 ≤ ∑ r ∈ Iic k, D r) (htot : ∑ r, D r = 0) :
    0 ≤ ∑ r, D r * ρ r := by
  set D' : ℕ → ℝ := fun j => if h : j < n then D ⟨j, h⟩ else 0 with hD'
  set ρ' : ℕ → ℝ := fun j => if h : j < n then ρ ⟨j, h⟩ else 0 with hρ'
  have e : ∑ r, D r * ρ r = ∑ j ∈ range n, ρ' j • D' j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ρ' j • D' j) n]
    apply sum_congr rfl
    intro r _
    simp [hD', hρ', r.isLt, mul_comm]
  have etot : ∑ j ∈ range n, D' j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range D' n, ← htot]
    apply sum_congr rfl
    intro r _
    simp [hD', r.isLt]
  rw [e, sum_range_by_parts, etot, smul_zero, zero_sub, neg_nonneg]
  apply sum_nonpos
  intro i hi
  rw [mem_range] at hi
  have hi1 : i + 1 < n := by omega
  have hi0 : i < n := by omega
  have hpart : 0 ≤ ∑ j ∈ range (i + 1), D' j := by
    have := hS ⟨i, hi0⟩
    rw [iic_sum_eq] at this
    simpa [hD'] using this
  have hdiff : ρ' (i + 1) - ρ' i ≤ 0 := by
    simp only [hρ', dif_pos hi1, dif_pos hi0]
    have : ρ ⟨i + 1, hi1⟩ ≤ ρ ⟨i, hi0⟩ := hρ (by simp [Fin.le_def])
    linarith
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg hdiff hpart

end ReportDepSPHonestyAux

open Finset ReportDepSP.Honesty in
theorem solution {n : ℕ} (P : (Fin n → Bool) → ℝ) (hP : IsAttainabilityDist P)
    (v : Fin n → ℝ) (hv : Antitone v) :
    (∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 →
      ((∀ ρ : Fin n → ℝ, StrictAnti ρ → payoff v ρ P Rt ≤ payoff v ρ P 1) ↔
        Condition3 P Rt)) ∧
    ((∀ ρ : Fin n → ℝ, StrictAnti ρ →
        ∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 → payoff v ρ P Rt ≤ payoff v ρ P 1) ↔
      ∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 → Condition3 P Rt) := by
  -- decomposition of the payoff
  have hdec : ∀ (ρ : Fin n → ℝ) (R : Equiv.Perm (Fin n)), payoff v ρ P R =
      ∑ r, matchProb P R r * v (R.symm r) + ∑ r, matchProb P R r * ρ r := by
    intro ρ R
    unfold payoff
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    ring
  have htot : ∀ Rt : Equiv.Perm (Fin n),
      ∑ r, (matchProb P 1 r - matchProb P Rt r) = 0 := by
    intro Rt
    rw [sum_sub_distrib, ReportDepSPHonestyAux.tot_matchProb P 1, ReportDepSPHonestyAux.tot_matchProb P Rt, sub_self]
  have key : ∀ Rt : Equiv.Perm (Fin n),
      ((∀ ρ : Fin n → ℝ, StrictAnti ρ → payoff v ρ P Rt ≤ payoff v ρ P 1) ↔
        Condition3 P Rt) := by
    intro Rt
    constructor
    · intro H k
      by_contra hneg
      push_neg at hneg
      set S := ∑ r ∈ Iic k, (matchProb P 1 r - matchProb P Rt r) with hSdef
      -- the family of test functions
      have hρM : ∀ M : ℝ, 0 ≤ M →
          StrictAnti (fun r : Fin n => -((r : ℕ) : ℝ) - M * (if k < r then 1 else 0)) := by
        intro M hM a b hab
        have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
        have hind : (if k < a then (1 : ℝ) else 0) ≤ (if k < b then 1 else 0) := by
          by_cases hka : k < a
          · rw [if_pos hka, if_pos (hka.trans hab)]
          · rw [if_neg hka]; split_ifs <;> norm_num
        have := mul_le_mul_of_nonneg_left hind hM
        simp only
        linarith
      -- the payoff difference is affine in M
      have hsplit : ∀ (R : Equiv.Perm (Fin n)) (M : ℝ),
          ∑ r, matchProb P R r * (-((r : ℕ) : ℝ) - M * (if k < r then 1 else 0)) =
            ∑ r, matchProb P R r * (-((r : ℕ) : ℝ)) -
              M * (∑ r, matchProb P R r - ∑ r ∈ Iic k, matchProb P R r) := by
        intro R M
        have hI : ∑ r ∈ Iic k, matchProb P R r =
            ∑ r, matchProb P R r * (if r ≤ k then 1 else 0) := by
          rw [← sum_filter_add_sum_filter_not univ (fun r => r ≤ k)]
          have h1 : univ.filter (fun r : Fin n => r ≤ k) = Iic k := by ext; simp
          rw [h1, sum_eq_zero (s := univ.filter (fun r : Fin n => ¬ r ≤ k))
            (fun r hr => by rw [mem_filter] at hr; rw [if_neg hr.2, mul_zero]), add_zero]
          apply sum_congr rfl
          intro r hr
          rw [mem_Iic] at hr
          rw [if_pos hr, mul_one]
        rw [hI, mul_sub]
        simp only [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro r _
        by_cases hkr : k < r
        · rw [if_pos hkr, if_neg (not_le.mpr hkr)]; ring
        · rw [if_neg hkr, if_pos (not_lt.mp hkr)]; ring
      set A := (∑ r, matchProb P 1 r * v ((1 : Equiv.Perm (Fin n)).symm r) +
          ∑ r, matchProb P 1 r * (-((r : ℕ) : ℝ))) -
        (∑ r, matchProb P Rt r * v (Rt.symm r) + ∑ r, matchProb P Rt r * (-((r : ℕ) : ℝ)))
        with hA
      have hdiff : ∀ M : ℝ, 0 ≤ M → 0 ≤ A + M * S := by
        intro M hM
        have h := H _ (hρM M hM)
        rw [hdec, hdec, hsplit, hsplit] at h
        have hT : ∑ r, matchProb P 1 r = ∑ r, matchProb P Rt r := by
          rw [ReportDepSPHonestyAux.tot_matchProb P 1, ReportDepSPHonestyAux.tot_matchProb P Rt]
        have hS' : S = ∑ r ∈ Iic k, matchProb P 1 r - ∑ r ∈ Iic k, matchProb P Rt r := by
          rw [hSdef, sum_sub_distrib]
        rw [hS', hA]
        rw [hT] at h
        nlinarith
      have hSneg : 0 < -S := by linarith
      have hM0 : 0 ≤ (|A| + 1) / (-S) := div_nonneg (by positivity) hSneg.le
      have := hdiff _ hM0
      have hcalc : (|A| + 1) / (-S) * S = -(|A| + 1) := by
        have hS0 : S ≠ 0 := hneg.ne
        rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hS0]
        ring
      rw [hcalc] at this
      have := le_abs_self A
      linarith
    · intro hC ρ hρ
      rw [hdec, hdec]
      have h1 := ReportDepSPHonestyAux.vpart_le P hP v hv Rt
      have h2 := ReportDepSPHonestyAux.abel_nonneg (fun r => matchProb P 1 r - matchProb P Rt r) ρ hρ.antitone
        (fun k => hC k) (htot Rt)
      have h3 : ∑ r, (matchProb P 1 r - matchProb P Rt r) * ρ r =
          ∑ r, matchProb P 1 r * ρ r - ∑ r, matchProb P Rt r * ρ r := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro r _
        ring
      linarith
  refine ⟨fun Rt _ => key Rt, ?_⟩
  constructor
  · intro H Rt hRt
    exact (key Rt).1 (fun ρ hρ => H ρ hρ Rt hRt)
  · intro H ρ hρ Rt hRt
    exact (key Rt).2 (H Rt hRt) ρ hρ
