-- Prove2me | solution 1 for OutpatientWalkIn.Triage.proposition_C_2_muS
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:41:49.385778+00:00
-- url     : https://prove2.me/submissions/c32bd711-452c-4b2e-898b-f3d45e6e3953

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OWTriageC2

open OutpatientWalkIn.SmallCap Finset Set Filter Topology

/-! ### Part 1: Basic properties of `aSeq`, `bSeq`, `Qf`, `Hh`, `aPrimeK`, and `Phi` -/

lemma aSeq_zero (ρ : ℝ) : aSeq ρ 0 = 1 := by rw [aSeq]

lemma aSeq_succ (ρ : ℝ) (n : ℕ) : aSeq ρ (n + 1) = Real.exp ρ *
    (aSeq ρ n - ∑ i ∈ Ico 1 (n + 1), alphaP ρ i * aSeq ρ (n + 1 - i) - alphaP ρ n) := by
  rw [aSeq, aSeq_zero, mul_one]
  congr 2
  rw [Finset.sum_attach (Ico 1 (n + 1)) (fun i => alphaP ρ i * aSeq ρ (n + 1 - i))]

lemma aSeq_one (ρ : ℝ) : aSeq ρ 1 = Real.exp ρ - 1 := by
  rw [aSeq_succ, aSeq_zero]
  simp [alphaP]
  rw [mul_sub, mul_one, ← Real.exp_add]; simp

lemma aSeq_rec_full (ρ : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), alphaP ρ i * aSeq ρ (m + 1 - i) + alphaP ρ m = aSeq ρ m := by
  have h := aSeq_succ ρ m
  have hsplit : ∑ i ∈ range (m + 1), alphaP ρ i * aSeq ρ (m + 1 - i) =
      alphaP ρ 0 * aSeq ρ (m + 1) + ∑ i ∈ Ico 1 (m + 1), alphaP ρ i * aSeq ρ (m + 1 - i) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 1 + i = i + 1 by ring]
  have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
  have he : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
  rw [hsplit, ha0, h]
  linear_combination (aSeq ρ m - ∑ i ∈ Ico 1 (m + 1), alphaP ρ i * aSeq ρ (m + 1 - i) -
    alphaP ρ m) * he

lemma aSeq_rec (ρ : ℝ) (k : ℕ) :
    alphaP ρ 0 * aSeq ρ (k + 2) + ∑ i ∈ range k, alphaP ρ (i + 1) * aSeq ρ (k + 1 - i)
      + Real.exp ρ * alphaP ρ (k + 1) = aSeq ρ (k + 1) := by
  have h := aSeq_succ ρ (k + 1)
  have hsplit : ∑ i ∈ Ico 1 (k + 1 + 1), alphaP ρ i * aSeq ρ (k + 1 + 1 - i) =
      ∑ i ∈ range k, alphaP ρ (i + 1) * aSeq ρ (k + 1 - i) + alphaP ρ (k + 1) * aSeq ρ 1 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [show k + 1 + 1 - 1 = k + 1 by omega]
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [show 1 + i = i + 1 by ring, show k + 1 + 1 - (i + 1) = k + 1 - i by omega]
    · rw [show 1 + k = k + 1 by ring, show k + 1 + 1 - (k + 1) = 1 by omega]
  rw [hsplit, aSeq_one] at h
  have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
  rw [ha0, h]
  have he : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
  linear_combination (aSeq ρ (k + 1) - (∑ i ∈ range k, alphaP ρ (i + 1) * aSeq ρ (k + 1 - i) +
      alphaP ρ (k + 1) * (Real.exp ρ - 1)) - alphaP ρ (k + 1)) * he

lemma bSeq_zero (ρ : ℝ) : bSeq ρ 0 = 1 := by simp [bSeq, aSeq_zero]

lemma bSeq_sub (ρ : ℝ) (i : ℕ) (hi : 1 ≤ i) : bSeq ρ i - bSeq ρ (i - 1) = aSeq ρ i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [bSeq, Finset.sum_range_succ]

lemma bSeq_succ (ρ : ℝ) (k : ℕ) : bSeq ρ (k + 1) = bSeq ρ k + aSeq ρ (k + 1) := by
  simp [bSeq, Finset.sum_range_succ]

noncomputable def Qf (i : ℕ) (x : ℝ) : ℝ :=
  (Real.exp x - ∑ m ∈ range (i + 1), x ^ m / (m.factorial : ℝ)) / x ^ (i + 1)

lemma Qf_succ (i : ℕ) (x : ℝ) (hx : x ≠ 0) :
    x * Qf (i + 1) x = Qf i x - 1 / ((i + 1).factorial : ℝ) := by
  unfold Qf
  rw [Finset.sum_range_succ (n := i + 1)]
  have hf : ((i + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma Qf_zero (x : ℝ) (hx : x ≠ 0) : x * Qf 0 x = Real.exp x - 1 := by
  unfold Qf; simp; field_simp

lemma Qf_hasSum (i : ℕ) (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => x ^ n / ((n + i + 1).factorial : ℝ)) (Qf i x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' (i + 1)).2 h
  have h3 := h2.div_const (x ^ (i + 1))
  have e : (fun n : ℕ => x ^ n / ((n + i + 1).factorial : ℝ)) =
      fun n => x ^ (n + (i + 1)) / ((n + (i + 1)).factorial : ℝ) / x ^ (i + 1) := by
    funext n
    have hxn : x ^ (i + 1) ≠ 0 := by positivity
    rw [show n + (i + 1) = n + i + 1 by ring, show n + i + 1 = n + (i + 1) by ring, pow_add]
    field_simp
  rw [e]
  exact h3

lemma Qf_pos (i : ℕ) (x : ℝ) (hx : 0 < x) : 0 < Qf i x := by
  have h := Qf_hasSum i x hx
  have h0pos : (0 : ℝ) < 1 / ((0 + i + 1).factorial : ℝ) := by positivity
  refine lt_of_lt_of_le h0pos ?_
  have h0 := sum_le_hasSum (Finset.range 1) (fun n _ => by positivity) h
  simpa using h0

lemma Qf_strictMono (i : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) : Qf i x < Qf i y := by
  have hy : 0 < y := lt_trans hx hxy
  refine hasSum_lt (f := fun n : ℕ => x ^ n / ((n + i + 1).factorial : ℝ))
    (g := fun n : ℕ => y ^ n / ((n + i + 1).factorial : ℝ)) (i := 1) ?_ ?_
    (Qf_hasSum i x hx) (Qf_hasSum i y hy)
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hx.le hxy.le n
  · simp only [pow_one]
    exact div_lt_div_of_pos_right hxy (by positivity)

lemma aP_one (p ρ : ℝ) : aPrimeK 1 p ρ = Real.exp (p * ρ) - 1 := by
  simp [aPrimeK]

lemma aP_rec (k : ℕ) (p ρ : ℝ) (hp : p ≠ 1) :
    aPrimeK (k + 2) p ρ = (aPrimeK (k + 1) p ρ
      - (1 - (1 - p) * Real.exp (p * ρ)) * aSeq ρ (k + 1)) / (1 - p) := by
  have hs : (1 - p) ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  unfold aPrimeK
  rw [show k + 2 = (k + 1) + 1 by ring, Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
  have hsum : ∑ i ∈ Ico 1 (k + 1), (bSeq ρ i - bSeq ρ (i - 1)) * ((1 - p) ^ (k + 1 + 1 - i))⁻¹ =
      (∑ i ∈ Ico 1 (k + 1), (bSeq ρ i - bSeq ρ (i - 1)) * ((1 - p) ^ (k + 1 - i))⁻¹) / (1 - p) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [show k + 1 + 1 - i = (k + 1 - i) + 1 by omega, pow_succ]
    field_simp
  rw [hsum, bSeq_sub ρ (k + 1) (by omega)]
  simp only [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
    show k + 1 + 1 - (k + 1) = 1 by omega, pow_succ]
  field_simp
  ring

noncomputable def Hh (ρ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ range k, aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) * Qf i (ρ * s)
    + ρ ^ (k + 1) * Qf k (ρ * s)

lemma Hh_key (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (s : ℝ) (hs : s ≠ 0) :
    s * Hh ρ (k + 1) s - Hh ρ k s =
      aSeq ρ (k + 2) * Real.exp (-ρ) * Real.exp (ρ * s) - aSeq ρ (k + 1) := by
  have hx : ρ * s ≠ 0 := mul_ne_zero hρ.ne' hs
  have hrec := aSeq_rec ρ k
  unfold Hh
  rw [Finset.sum_range_succ']
  have hterm : ∀ i ∈ range k, s * (aSeq ρ (k + 1 + 1 - (i + 1)) * Real.exp (-ρ) * ρ ^ (i + 1 + 1)
      * Qf (i + 1) (ρ * s)) = aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) * Qf i (ρ * s)
        - alphaP ρ (i + 1) * aSeq ρ (k + 1 - i) := by
    intro i _
    rw [show k + 1 + 1 - (i + 1) = k + 1 - i by omega]
    have h1 := Qf_succ i (ρ * s) hx
    have hrew : s * (aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) (ρ * s)) =
        aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) * ((ρ * s) * Qf (i + 1) (ρ * s)) := by
      ring
    rw [hrew, h1]
    simp only [alphaP]
    ring
  have hsum : s * ∑ i ∈ range k, aSeq ρ (k + 1 + 1 - (i + 1)) * Real.exp (-ρ) * ρ ^ (i + 1 + 1)
      * Qf (i + 1) (ρ * s) = ∑ i ∈ range k, aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) *
        Qf i (ρ * s) - ∑ i ∈ range k, alphaP ρ (i + 1) * aSeq ρ (k + 1 - i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have h0 : s * (aSeq ρ (k + 1 + 1 - 0) * Real.exp (-ρ) * ρ ^ (0 + 1) * Qf 0 (ρ * s)) =
      aSeq ρ (k + 2) * Real.exp (-ρ) * (Real.exp (ρ * s) - 1) := by
    rw [← Qf_zero (ρ * s) hx]; simp only [show k + 1 + 1 - 0 = k + 2 by omega]; ring
  have hlast : s * (ρ ^ (k + 1 + 1) * Qf (k + 1) (ρ * s)) =
      ρ ^ (k + 1) * Qf k (ρ * s) - ρ ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    have h1 := Qf_succ k (ρ * s) hx
    have hrew : s * (ρ ^ (k + 1 + 1) * Qf (k + 1) (ρ * s)) =
        ρ ^ (k + 1) * ((ρ * s) * Qf (k + 1) (ρ * s)) := by
      ring
    rw [hrew, h1]; ring
  rw [mul_add, mul_add, hsum, h0, hlast]
  have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
  have hak : Real.exp ρ * alphaP ρ (k + 1) = ρ ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    simp only [alphaP]
    have he : Real.exp ρ * Real.exp (-ρ) = 1 := by rw [← Real.exp_add]; simp
    rw [← mul_div_assoc, ← mul_assoc, he, one_mul]
  rw [ha0, hak] at hrec
  linear_combination -hrec

lemma aP_eq (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
    aPrimeK (k + 1) p ρ = aSeq ρ (k + 1) - Real.exp (p * ρ) * (1 - p) * Hh ρ k (1 - p) := by
  have hs : (1 - p) ≠ 0 := by linarith
  have hx : ρ * (1 - p) ≠ 0 := mul_ne_zero hρ.ne' hs
  have hee : Real.exp (p * ρ) * Real.exp (ρ * (1 - p)) = Real.exp ρ := by
    rw [← Real.exp_add]; ring_nf
  have hee' : Real.exp (p * ρ) * Real.exp (-ρ) * Real.exp (ρ * (1 - p)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  induction k with
  | zero =>
    rw [aP_one, aSeq_one]
    unfold Hh
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one]
    have h := Qf_zero (ρ * (1 - p)) hx
    have hrew : Real.exp (p * ρ) * (1 - p) * (ρ * Qf 0 (ρ * (1 - p))) =
        Real.exp (p * ρ) * (ρ * (1 - p) * Qf 0 (ρ * (1 - p))) := by ring
    rw [hrew, h]
    linear_combination hee
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by ring, aP_rec k p ρ (by linarith), ih]
    have hkey := Hh_key ρ hρ k (1 - p) hs
    rw [div_eq_iff hs]
    linear_combination (Real.exp (p * ρ) * (1 - p)) * hkey + ((1 - p) * aSeq ρ (k + 2)) * hee'

lemma aP_zero (k : ℕ) (ρ : ℝ) : aPrimeK (k + 1) 0 ρ = 0 := by
  simp [aPrimeK]

lemma a_eq_Hh (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : aSeq ρ (k + 1) = Hh ρ k 1 := by
  have h := aP_eq ρ hρ k 0 (by norm_num)
  rw [aP_zero] at h
  simp at h
  linarith

lemma aSeq_pos (ρ : ℝ) (hρ : 0 < ρ) : ∀ n, 0 < aSeq ρ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · rw [aSeq_zero]; norm_num
    rw [a_eq_Hh ρ hρ k]
    rcases k with _ | m
    · unfold Hh; simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact mul_pos (by positivity) (Qf_pos 0 _ (by positivity))
    · have hsplit : Hh ρ (m + 1) 1 = aSeq ρ (m + 2) * (1 - Real.exp (-ρ)) +
          (∑ i ∈ range m, aSeq ρ (m + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) ρ
            + ρ ^ (m + 1 + 1) * Qf (m + 1) ρ) := by
        unfold Hh
        rw [Finset.sum_range_succ']
        have hq := Qf_zero ρ hρ.ne'
        simp only [mul_one, show m + 1 + 1 - 0 = m + 2 by omega, zero_add, pow_one]
        have he : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
        have e2 : ∀ i ∈ range m, aSeq ρ (m + 1 + 1 - (i + 1)) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) *
            Qf (i + 1) ρ = aSeq ρ (m + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) ρ := by
          intro i _; rw [show m + 1 + 1 - (i + 1) = m + 1 - i by omega]
        rw [Finset.sum_congr rfl e2]
        linear_combination (aSeq ρ (m + 2) * Real.exp (-ρ)) * hq + aSeq ρ (m + 2) * he
      have hR : 0 < ∑ i ∈ range m, aSeq ρ (m + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) ρ
            + ρ ^ (m + 1 + 1) * Qf (m + 1) ρ := by
        apply add_pos_of_nonneg_of_pos
        · apply Finset.sum_nonneg
          intro i hi
          have := ih (m + 1 - i) (by omega)
          have := Qf_pos (i + 1) ρ hρ
          positivity
        · exact mul_pos (by positivity) (Qf_pos _ _ hρ)
      have hA := a_eq_Hh ρ hρ (m + 1)
      rw [show m + 1 + 1 = m + 2 by rfl] at hA
      have he : 0 < Real.exp (-ρ) := Real.exp_pos _
      have h3 : 0 < aSeq ρ (m + 2) * Real.exp (-ρ) := by
        rw [hsplit] at hA; linarith
      have h4 : 0 < aSeq ρ (m + 2) := by
        by_contra h; push Not at h
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h he.le]
      rw [← hA]; exact h4

lemma Hh_pos (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (s : ℝ) (hs : 0 < s) : 0 < Hh ρ k s := by
  unfold Hh
  apply add_pos_of_nonneg_of_pos
  · apply Finset.sum_nonneg
    intro i _
    have := aSeq_pos ρ hρ (k + 1 - i)
    have := Qf_pos i (ρ * s) (by positivity)
    positivity
  · exact mul_pos (by positivity) (Qf_pos _ _ (by positivity))

lemma Hh_strictMono (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    Hh ρ k s < Hh ρ k t := by
  unfold Hh
  have hx : 0 < ρ * s := by positivity
  have hxy : ρ * s < ρ * t := mul_lt_mul_of_pos_left hst hρ
  apply add_lt_add_of_le_of_lt
  · apply Finset.sum_le_sum
    intro i _
    have := aSeq_pos ρ hρ (k + 1 - i)
    have := (Qf_strictMono i hx hxy).le
    have h0 : 0 ≤ aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  · exact mul_lt_mul_of_pos_left (Qf_strictMono k hx hxy) (by positivity)

lemma Hh_le (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Hh ρ k s ≤ aSeq ρ (k + 1) := by
  rw [a_eq_Hh ρ hρ k]
  rcases eq_or_lt_of_le hs1 with h | h
  · rw [h]
  · exact (Hh_strictMono ρ hρ k hs h).le

lemma aP_succ_form (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
    aPrimeK (k + 2) p ρ = Real.exp (p * ρ) * (aSeq ρ (k + 1) - Hh ρ k (1 - p)) := by
  have hs : (1 - p) ≠ 0 := by linarith
  rw [aP_rec k p ρ (by linarith), aP_eq ρ hρ k p hp, div_eq_iff hs]
  ring

lemma aP_lt (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
    aPrimeK (k + 1) p ρ < aSeq ρ (k + 1) := by
  rw [aP_eq ρ hρ k p hp]
  have := Hh_pos ρ hρ k (1 - p) (by linarith)
  have : 0 < 1 - p := by linarith
  have : 0 < Real.exp (p * ρ) * (1 - p) * Hh ρ k (1 - p) := by positivity
  linarith

lemma aP_strictMono (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hq : q < 1) : aPrimeK (k + 1) p ρ < aPrimeK (k + 1) q ρ := by
  rcases k with _ | m
  · rw [aP_one, aP_one]
    have := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_right hpq hρ)
    linarith
  · rw [aP_succ_form ρ hρ m p (by linarith), aP_succ_form ρ hρ m q hq]
    have h1 : Hh ρ m (1 - q) < Hh ρ m (1 - p) := Hh_strictMono ρ hρ m (by linarith) (by linarith)
    have h2 : Hh ρ m (1 - p) ≤ aSeq ρ (m + 1) := Hh_le ρ hρ m (by linarith) (by linarith)
    have h3 : Real.exp (p * ρ) ≤ Real.exp (q * ρ) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hpq.le hρ.le)
    have hX : 0 ≤ aSeq ρ (m + 1) - Hh ρ m (1 - p) := by linarith
    calc Real.exp (p * ρ) * (aSeq ρ (m + 1) - Hh ρ m (1 - p))
        ≤ Real.exp (q * ρ) * (aSeq ρ (m + 1) - Hh ρ m (1 - p)) :=
          mul_le_mul_of_nonneg_right h3 hX
      _ < Real.exp (q * ρ) * (aSeq ρ (m + 1) - Hh ρ m (1 - q)) :=
          mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos _)

lemma aP_nonneg (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    0 ≤ aPrimeK (k + 1) p ρ := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h, aP_zero]
  · rw [← aP_zero k ρ]; exact (aP_strictMono ρ hρ k le_rfl h hp1).le

lemma aP_close (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    aSeq ρ (k + 1) - aPrimeK (k + 1) p ρ ≤ Real.exp ρ * aSeq ρ (k + 1) * (1 - p) := by
  rw [aP_eq ρ hρ k p hp1]
  have h1 := Hh_le ρ hρ k (s := 1 - p) (by linarith) (by linarith)
  have h2 : Real.exp (p * ρ) ≤ Real.exp ρ := Real.exp_le_exp.2 (by nlinarith)
  have h3 := Hh_pos ρ hρ k (1 - p) (by linarith)
  have h4 : 0 ≤ 1 - p := by linarith
  have hmul : Real.exp (p * ρ) * (1 - p) * Hh ρ k (1 - p) ≤
      Real.exp ρ * (1 - p) * aSeq ρ (k + 1) := by
    apply mul_le_mul _ h1 h3.le (by positivity)
    exact mul_le_mul_of_nonneg_right h2 h4
  linarith

noncomputable def Gk (ρ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if t = 1 then aSeq ρ (k + 1) else aPrimeK (k + 1) t ρ

lemma Gk_zero (ρ : ℝ) (k : ℕ) : Gk ρ k 0 = 0 := by simp [Gk, aP_zero]

lemma Gk_one (ρ : ℝ) (k : ℕ) : Gk ρ k 1 = aSeq ρ (k + 1) := by simp [Gk]

lemma Gk_strictMonoOn (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : StrictMonoOn (Gk ρ k) (Icc 0 1) := by
  intro t ht t' ht' htt
  have ht1 : t ≠ 1 := by intro h; rw [h] at htt; linarith [ht'.2]
  rcases eq_or_lt_of_le ht'.2 with h | h
  · rw [h, Gk_one]; simp only [Gk, ht1, if_false]
    exact aP_lt ρ hρ k t (by rw [← h]; exact htt)
  · simp only [Gk, ht1, h.ne, if_false]
    exact aP_strictMono ρ hρ k ht.1 htt h

noncomputable def Phi (ρ : ℝ) (x : ℝ) : ℝ := bSeq ρ ⌊x⌋₊ + Gk ρ ⌊x⌋₊ (x - ⌊x⌋₊)

lemma Phi_eq (ρ : ℝ) (k : ℕ) (x : ℝ) (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    Phi ρ x = bSeq ρ k + Gk ρ k (x - k) := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hf : ⌊x⌋₊ = k + 1 := by rw [h]; exact_mod_cast Nat.floor_natCast (R := ℝ) (k + 1)
    unfold Phi
    rw [hf, h]; push_cast
    rw [sub_self, Gk_zero, show (k : ℝ) + 1 - k = 1 by ring, Gk_one, bSeq_succ]; ring
  · have hf : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
      exact ⟨hx.1, h⟩
    unfold Phi; rw [hf]

lemma q0_eq (ρ : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    q0 ⌈x⌉₊ (x + 1 - ⌈x⌉₊) ρ = 1 / Phi ρ x := by
  set k := ⌊x⌋₊ with hk
  have hk1 : (k : ℝ) ≤ x := Nat.floor_le hx
  have hk2 : x < k + 1 := Nat.lt_floor_add_one x
  rcases eq_or_lt_of_le hk1 with h | h
  · have hc : ⌈x⌉₊ = k := by rw [← h]; exact Nat.ceil_natCast k
    have hPhi : Phi ρ x = bSeq ρ k := by
      rw [Phi_eq ρ k x ⟨hk1, hk2.le⟩, ← h, sub_self, Gk_zero, add_zero]
    rw [hPhi, hc]
    unfold q0
    rw [if_pos (by rw [← h]; ring)]
  · have hc : ⌈x⌉₊ = k + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      simp only [Nat.add_sub_cancel]; push_cast
      exact ⟨h, hk2.le⟩
    have hPhi : Phi ρ x = bSeq ρ k + aPrimeK (k + 1) (x - k) ρ := by
      rw [Phi_eq ρ k x ⟨hk1, hk2.le⟩]
      simp only [Gk, show x - k ≠ 1 by intro h'; linarith, if_false]
    rw [hPhi, hc]
    unfold q0
    push_cast
    rw [if_neg (by intro h'; linarith), show x + 1 - ((k : ℝ) + 1) = x - k by ring]

lemma bSeq_mono (ρ : ℝ) (hρ : 0 < ρ) {m n : ℕ} (h : m ≤ n) : bSeq ρ m ≤ bSeq ρ n := by
  induction h with
  | refl => exact le_rfl
  | @step n _ ih =>
    rw [bSeq_succ]
    linarith [aSeq_pos ρ hρ (n + 1)]

lemma bSeq_ge_one (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : 1 ≤ bSeq ρ k := by
  rw [← bSeq_zero ρ]
  exact bSeq_mono ρ hρ (Nat.zero_le k)

lemma Phi_ge_one (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ Phi ρ x := by
  have hk1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hk2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  rw [Phi_eq ρ ⌊x⌋₊ x ⟨hk1, hk2.le⟩]
  simp only [Gk, show x - ⌊x⌋₊ ≠ 1 by linarith, if_false]
  linarith [bSeq_ge_one ρ hρ ⌊x⌋₊,
    aP_nonneg ρ hρ ⌊x⌋₊ (p := x - ⌊x⌋₊) (by linarith) (by linarith)]

lemma Phi_strictMonoOn_piece (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    StrictMonoOn (Phi ρ) (Icc (k : ℝ) (k + 1)) := by
  intro x hx y hy hxy
  rw [Phi_eq ρ k x hx, Phi_eq ρ k y hy]
  have := Gk_strictMonoOn ρ hρ k ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith : x - k < y - k)
  linarith

lemma Phi_strictMonoOn (ρ : ℝ) (hρ : 0 < ρ) : StrictMonoOn (Phi ρ) (Ici 0) := by
  have key : ∀ m : ℕ, ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ m → Phi ρ x < Phi ρ y := by
    intro m
    induction m with
    | zero => intro x y hx hxy hy; simp at hy; linarith
    | succ m ih =>
      intro x y hx hxy hy
      by_cases hym : y ≤ m
      · exact ih x y hx hxy hym
      push Not at hym
      push_cast at hy
      by_cases hxm : (m : ℝ) ≤ x
      · exact Phi_strictMonoOn_piece ρ hρ m ⟨hxm, by linarith⟩ ⟨by linarith, hy⟩ hxy
      push Not at hxm
      have h1 := ih x m hx hxm le_rfl
      have h2 := Phi_strictMonoOn_piece ρ hρ m ⟨le_rfl, by linarith⟩ ⟨hym.le, hy⟩ hym
      linarith
  intro x hx y hy hxy
  exact key ⌈y⌉₊ x y hx hxy (Nat.le_ceil y)

lemma triage_blockProb_eq (lam δ μS : ℝ) (hδ : 0 ≤ δ) (hμS : 0 < μS) :
    OutpatientWalkIn.Triage.blockProb lam δ μS =
      1 - 1 / (1 / Phi (lam / μS) (δ * μS) + lam / μS) := by
  unfold OutpatientWalkIn.Triage.blockProb
  rw [if_neg (by push Not; exact ⟨hμS, hδ⟩)]
  rw [q0_eq (lam / μS) (δ * μS) (by positivity)]

/-! ### Part 2: Exact derivatives in `ρ` and strict monotonicity of `1 / Φ(ρ, x) + ρ` -/

lemma hasDerivAt_congr_deriv {f : ℝ → ℝ} {d₁ d₂ x : ℝ}
    (h : HasDerivAt f d₁ x) (heq : d₁ = d₂) : HasDerivAt f d₂ x :=
  heq ▸ h

lemma hasDerivAt_alphaP_zero (ρ : ℝ) :
    HasDerivAt (fun r => alphaP r 0) (-alphaP ρ 0) ρ := by
  have heq : (fun r => alphaP r 0) = fun r => Real.exp (-r) := by
    funext r; simp [alphaP]
  rw [heq]
  have h := (Real.hasDerivAt_exp (-ρ)).comp ρ (hasDerivAt_id ρ).neg
  refine hasDerivAt_congr_deriv h ?_
  simp [alphaP]

lemma hasDerivAt_alphaP_succ (n : ℕ) (ρ : ℝ) :
    HasDerivAt (fun r => alphaP r (n + 1)) (alphaP ρ n - alphaP ρ (n + 1)) ρ := by
  have he : HasDerivAt (fun r => Real.exp (-r)) (-Real.exp (-ρ)) ρ :=
    hasDerivAt_congr_deriv ((Real.hasDerivAt_exp (-ρ)).comp ρ (hasDerivAt_id ρ).neg) (by ring)
  have hp : HasDerivAt (fun r => r ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * ρ ^ n) ρ := by
    simpa using hasDerivAt_pow (n + 1) ρ
  have hmul := he.mul hp
  have hdiv := hmul.div_const (((n + 1).factorial : ℝ))
  have hfact : (((n + 1).factorial : ℝ)) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfn : (fun r => alphaP r (n + 1)) =
      fun r => Real.exp (-r) * r ^ (n + 1) / ((n + 1).factorial : ℝ) := rfl
  rw [hfn]
  refine hasDerivAt_congr_deriv hdiv ?_
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [alphaP, hfact]
  field_simp
  ring

lemma sum_triangle_swap (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range (n - i), F i j =
      ∑ j ∈ range n, ∑ i ∈ range (n - j), F i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i), F i j =
        (∑ i ∈ range n, ∑ j ∈ range (n - i), F i j) + ∑ i ∈ range (n + 1), F i (n - i) := by
      rw [Finset.sum_range_succ (n := n), Finset.sum_range_succ (n := n)]
      have hsub : ∑ i ∈ range n, ∑ j ∈ range (n + 1 - i), F i j =
          ∑ i ∈ range n, ((∑ j ∈ range (n - i), F i j) + F i (n - i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [show n + 1 - i = (n - i) + 1 by omega, Finset.sum_range_succ]
      rw [hsub, Finset.sum_add_distrib]
      simp only [show n + 1 - n = 1 by omega, Finset.sum_range_one, Nat.sub_self]
      ring
    have hR : ∑ j ∈ range (n + 1), ∑ i ∈ range (n + 1 - j), F i j =
        (∑ j ∈ range n, ∑ i ∈ range (n - j), F i j) + ∑ j ∈ range (n + 1), F (n - j) j := by
      rw [Finset.sum_range_succ (n := n), Finset.sum_range_succ (n := n)]
      have hsub : ∑ j ∈ range n, ∑ i ∈ range (n + 1 - j), F i j =
          ∑ j ∈ range n, ((∑ i ∈ range (n - j), F i j) + F (n - j) j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ]
      rw [hsub, Finset.sum_add_distrib]
      simp only [show n + 1 - n = 1 by omega, Finset.sum_range_one, Nat.sub_self]
      ring
    rw [hL, hR, ih]
    congr 1
    have href := Finset.sum_range_reflect (fun i => F i (n - i)) (n + 1)
    rw [← href]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]

noncomputable def aDeriv (ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ∑ j ∈ range (n + 1), aSeq ρ j * aSeq ρ (n + 1 - j) + aSeq ρ n

lemma aDeriv_rec (ρ : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), alphaP ρ i * aDeriv ρ (m + 1 - i) =
      ∑ j ∈ range (m + 1), aSeq ρ j * aSeq ρ (m - j) := by
  have h1 : ∑ i ∈ range (m + 1), alphaP ρ i * aDeriv ρ (m + 1 - i) =
      (∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1 - i), alphaP ρ i * (aSeq ρ j * aSeq ρ (m + 1 - i - j))) +
        ∑ i ∈ range (m + 1), alphaP ρ i * aSeq ρ (m - i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hmi : m + 1 - i = (m - i) + 1 := by omega
    rw [hmi, aDeriv, mul_add, Finset.mul_sum]
  rw [h1, sum_triangle_swap (m + 1) (fun i j => alphaP ρ i * (aSeq ρ j * aSeq ρ (m + 1 - i - j)))]
  have h2 : ∑ j ∈ range (m + 1), ∑ i ∈ range (m + 1 - j),
        alphaP ρ i * (aSeq ρ j * aSeq ρ (m + 1 - i - j)) =
      ∑ j ∈ range (m + 1), aSeq ρ j * (aSeq ρ (m - j) - alphaP ρ (m - j)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hinner : ∑ i ∈ range (m + 1 - j), alphaP ρ i * (aSeq ρ j * aSeq ρ (m + 1 - i - j)) =
        aSeq ρ j * ∑ i ∈ range ((m - j) + 1), alphaP ρ i * aSeq ρ ((m - j) + 1 - i) := by
      rw [show m + 1 - j = (m - j) + 1 by omega, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show m + 1 - i - j = m - j + 1 - i by omega]
      ring
    rw [hinner]
    have hrec := aSeq_rec_full ρ (m - j)
    congr 1
    linarith
  rw [h2]
  have h3 : ∑ j ∈ range (m + 1), aSeq ρ j * (aSeq ρ (m - j) - alphaP ρ (m - j)) =
      (∑ j ∈ range (m + 1), aSeq ρ j * aSeq ρ (m - j)) -
        ∑ j ∈ range (m + 1), aSeq ρ j * alphaP ρ (m - j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => mul_sub _ _ _
  rw [h3]
  have href : ∑ j ∈ range (m + 1), aSeq ρ j * alphaP ρ (m - j) =
      ∑ i ∈ range (m + 1), alphaP ρ i * aSeq ρ (m - i) := by
    rw [← Finset.sum_range_reflect (fun j => aSeq ρ j * alphaP ρ (m - j)) (m + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp only [show m + 1 - 1 - i = m - i by omega, show m - (m - i) = i by omega]
    ring
  rw [href]
  ring

lemma hasDerivAt_aSeq : ∀ (n : ℕ) (ρ : ℝ), HasDerivAt (fun r => aSeq r n) (aDeriv ρ n) ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ
    rcases n with _ | m
    · have h : (fun r => aSeq r 0) = fun _ => (1 : ℝ) := funext aSeq_zero
      rw [h]; exact hasDerivAt_const ρ 1
    · have hfn : (fun r => aSeq r (m + 1)) = fun r => Real.exp r *
          (aSeq r m - ∑ i ∈ Ico 1 (m + 1), alphaP r i * aSeq r (m + 1 - i) - alphaP r m) :=
        funext fun r => aSeq_succ r m
      rw [hfn]
      have hsum_deriv : HasDerivAt
          (fun r => ∑ i ∈ Ico 1 (m + 1), alphaP r i * aSeq r (m + 1 - i))
          (∑ i ∈ Ico 1 (m + 1),
            ((alphaP ρ (i - 1) - alphaP ρ i) * aSeq ρ (m + 1 - i) +
              alphaP ρ i * aDeriv ρ (m + 1 - i))) ρ := by
        apply HasDerivAt.fun_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have ha : HasDerivAt (fun r => alphaP r i) (alphaP ρ (i - 1) - alphaP ρ i) ρ := by
          obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          simpa using hasDerivAt_alphaP_succ k ρ
        have hb : HasDerivAt (fun r => aSeq r (m + 1 - i)) (aDeriv ρ (m + 1 - i)) ρ :=
          ih (m + 1 - i) (by omega) ρ
        exact ha.mul hb
      have hm_deriv : HasDerivAt (fun r => aSeq r m) (aDeriv ρ m) ρ := ih m (by omega) ρ
      rcases m with _ | r
      · have hF := (hm_deriv.sub hsum_deriv).sub (hasDerivAt_alphaP_zero ρ)
        have htot := (Real.hasDerivAt_exp ρ).mul hF
        refine hasDerivAt_congr_deriv htot ?_
        simp only [Pi.sub_apply, Ico_self, Finset.sum_empty, sub_zero, aSeq_zero, aDeriv]
        rw [Finset.sum_range_one, Nat.sub_zero, aSeq_zero, aSeq_one]
        ring
      · have hF := (hm_deriv.sub hsum_deriv).sub (hasDerivAt_alphaP_succ r ρ)
        have htot := (Real.hasDerivAt_exp ρ).mul hF
        refine hasDerivAt_congr_deriv htot ?_
        simp only [Pi.sub_apply]
        have hsum_cancel :
            (∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ i * aSeq ρ (r + 1 + 1 - i)) +
            ∑ i ∈ Ico 1 (r + 1 + 1),
              ((alphaP ρ (i - 1) - alphaP ρ i) * aSeq ρ (r + 1 + 1 - i) +
                alphaP ρ i * aDeriv ρ (r + 1 + 1 - i)) =
            (∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ (i - 1) * aSeq ρ (r + 1 + 1 - i)) +
              ∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ i * aDeriv ρ (r + 1 + 1 - i) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        have hshift : ∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ (i - 1) * aSeq ρ (r + 1 + 1 - i) =
            ∑ j ∈ range (r + 1), alphaP ρ j * aSeq ρ (r + 1 - j) := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [show r + 1 + 1 - 1 = r + 1 by omega]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show 1 + j - 1 = j by omega, show r + 1 + 1 - (1 + j) = r + 1 - j by omega]
        have hrec_r := aSeq_rec_full ρ r
        have hdrec := aDeriv_rec ρ (r + 1)
        have hdrec_split : ∑ i ∈ range (r + 1 + 1), alphaP ρ i * aDeriv ρ (r + 1 + 1 - i) =
            alphaP ρ 0 * aDeriv ρ (r + 2) +
              ∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ i * aDeriv ρ (r + 1 + 1 - i) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero]
          rw [add_comm]
          congr 1
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [show r + 1 + 1 - 1 = r + 1 by omega]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show 1 + j = j + 1 by ring]
        have hrhs_split : ∑ j ∈ range (r + 1 + 1), aSeq ρ j * aSeq ρ (r + 1 - j) =
            aDeriv ρ (r + 1) - aSeq ρ r + aSeq ρ (r + 1) := by
          rw [Finset.sum_range_succ, Nat.sub_self, aSeq_zero, mul_one, aDeriv]
          ring
        have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
        have he : Real.exp ρ * Real.exp (-ρ) = 1 := by rw [← Real.exp_add]; simp
        have hinner :
            (aSeq ρ (r + 1) - ∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ i * aSeq ρ (r + 1 + 1 - i) -
                alphaP ρ (r + 1)) +
            (aDeriv ρ (r + 1) -
              ∑ i ∈ Ico 1 (r + 1 + 1),
                ((alphaP ρ (i - 1) - alphaP ρ i) * aSeq ρ (r + 1 + 1 - i) +
                  alphaP ρ i * aDeriv ρ (r + 1 + 1 - i)) -
              (alphaP ρ r - alphaP ρ (r + 1))) =
            Real.exp (-ρ) * aDeriv ρ (r + 2) := by
          rw [hdrec_split, hrhs_split, ha0] at hdrec
          linarith [hsum_cancel, hshift, hrec_r, hdrec]
        have hrew : Real.exp ρ *
            (aSeq ρ (r + 1) - ∑ i ∈ Ico 1 (r + 1 + 1), alphaP ρ i * aSeq ρ (r + 1 + 1 - i) -
              alphaP ρ (r + 1)) +
            Real.exp ρ *
            (aDeriv ρ (r + 1) -
              ∑ i ∈ Ico 1 (r + 1 + 1),
                ((alphaP ρ (i - 1) - alphaP ρ i) * aSeq ρ (r + 1 + 1 - i) +
                  alphaP ρ i * aDeriv ρ (r + 1 + 1 - i)) -
              (alphaP ρ r - alphaP ρ (r + 1))) =
            Real.exp ρ * (Real.exp (-ρ) * aDeriv ρ (r + 2)) := by
          rw [← mul_add, hinner]
        rw [hrew, ← mul_assoc, he, one_mul]

noncomputable def bDeriv (ρ : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range k, aSeq ρ j * bSeq ρ (k - j)

lemma hasDerivAt_bSeq (k : ℕ) (ρ : ℝ) :
    HasDerivAt (fun r => bSeq r k) (bDeriv ρ k) ρ := by
  induction k with
  | zero =>
    have h : (fun r => bSeq r 0) = fun _ => (1 : ℝ) := funext bSeq_zero
    rw [h]; simp [bDeriv]; exact hasDerivAt_const ρ 1
  | succ k ih =>
    have hfn : (fun r => bSeq r (k + 1)) = fun r => bSeq r k + aSeq r (k + 1) :=
      funext fun r => bSeq_succ r k
    rw [hfn]
    refine hasDerivAt_congr_deriv (ih.add (hasDerivAt_aSeq (k + 1) ρ)) ?_
    unfold bDeriv
    rw [Finset.sum_range_succ, aDeriv]
    rw [Finset.sum_range_succ]
    have hcomb : (∑ j ∈ range k, aSeq ρ j * bSeq ρ (k - j)) +
        ∑ j ∈ range k, aSeq ρ j * aSeq ρ (k + 1 - j) =
        ∑ j ∈ range k, aSeq ρ j * bSeq ρ (k + 1 - j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show k + 1 - j = (k - j) + 1 by omega, bSeq_succ]
      ring
    have hb1 : bSeq ρ 1 = aSeq ρ 1 + 1 := by
      rw [bSeq_succ, bSeq_zero]; ring
    simp only [show k + 1 - k = 1 by omega, hb1]
    linarith

noncomputable def PhiK (k : ℕ) (p ρ : ℝ) : ℝ := bSeq ρ k + aPrimeK (k + 1) p ρ

lemma PhiK_zero (p ρ : ℝ) : PhiK 0 p ρ = Real.exp (p * ρ) := by
  unfold PhiK; rw [bSeq_zero, aP_one]; ring

lemma PhiK_rec (k : ℕ) (p ρ : ℝ) (hp : p ≠ 1) :
    (1 - p) * PhiK (k + 1) p ρ =
      PhiK k p ρ - p * bSeq ρ (k + 1) + (1 - p) * Real.exp (p * ρ) * aSeq ρ (k + 1) := by
  have hs : 1 - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  unfold PhiK
  rw [show k + 1 + 1 = k + 2 by ring, aP_rec k p ρ hp, bSeq_succ ρ k]
  field_simp
  ring

noncomputable def PhiKDeriv (k : ℕ) (p ρ : ℝ) : ℝ :=
  ∑ j ∈ range k, aSeq ρ j * PhiK (k - j) p ρ + p * aSeq ρ k * Real.exp (p * ρ)

lemma hasDerivAt_PhiK (k : ℕ) (p : ℝ) (hp : p ≠ 1) (ρ : ℝ) :
    HasDerivAt (fun r => PhiK k p r) (PhiKDeriv k p ρ) ρ := by
  have hs : 1 - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  induction k with
  | zero =>
    have hfn : (fun r => PhiK 0 p r) = fun r => Real.exp (p * r) := funext fun r => PhiK_zero p r
    rw [hfn]
    have h1 : HasDerivAt (fun r => p * r) (p * 1) ρ := (hasDerivAt_id ρ).const_mul p
    refine hasDerivAt_congr_deriv ((Real.hasDerivAt_exp (p * ρ)).comp ρ h1) ?_
    simp [PhiKDeriv, aSeq_zero]
    ring
  | succ k ih =>
    have hfn : (fun r => PhiK (k + 1) p r) = fun r =>
        (PhiK k p r - p * bSeq r (k + 1) + (1 - p) * Real.exp (p * r) * aSeq r (k + 1)) / (1 - p) := by
      funext r
      rw [eq_div_iff hs, mul_comm]
      exact PhiK_rec k p r hp
    rw [hfn]
    have h1 : HasDerivAt (fun r => p * r) (p * 1) ρ := (hasDerivAt_id ρ).const_mul p
    have hexp : HasDerivAt (fun r => Real.exp (p * r)) (Real.exp (p * ρ) * p) ρ :=
      hasDerivAt_congr_deriv ((Real.hasDerivAt_exp (p * ρ)).comp ρ h1) (by ring)
    have hterm := ((hexp.const_mul (1 - p)).mul (hasDerivAt_aSeq (k + 1) ρ))
    have hnum := (ih.sub ((hasDerivAt_bSeq (k + 1) ρ).const_mul p)).add hterm
    refine hasDerivAt_congr_deriv (hnum.div_const (1 - p)) ?_
    rw [div_eq_iff hs]
    symm
    rw [mul_comm]
    -- Compute `(1 - p) * PhiKDeriv (k + 1) p ρ`
    unfold PhiKDeriv
    rw [mul_add, Finset.mul_sum]
    have hsum : ∑ j ∈ range (k + 1), (1 - p) * (aSeq ρ j * PhiK (k + 1 - j) p ρ) =
        (∑ j ∈ range (k + 1), aSeq ρ j * PhiK (k - j) p ρ) -
        p * (∑ j ∈ range (k + 1), aSeq ρ j * bSeq ρ (k + 1 - j)) +
        (1 - p) * Real.exp (p * ρ) * (∑ j ∈ range (k + 1), aSeq ρ j * aSeq ρ (k + 1 - j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hkj : k + 1 - j = (k - j) + 1 := by omega
      rw [hkj]
      have hrec := PhiK_rec (k - j) p ρ hp
      linear_combination aSeq ρ j * hrec
    rw [hsum, Finset.sum_range_succ (f := fun j => aSeq ρ j * PhiK (k - j) p ρ)]
    simp only [Nat.sub_self, PhiK_zero]
    unfold bDeriv
    rw [aDeriv]
    ring

lemma PhiK_strictMono_k (ρ : ℝ) (hρ : 0 < ρ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    {r s : ℕ} (hrs : r < s) : PhiK r p ρ < PhiK s p ρ := by
  unfold PhiK
  have h1 : aPrimeK (r + 1) p ρ < aSeq ρ (r + 1) := aP_lt ρ hρ r p hp1
  have h2 : bSeq ρ (r + 1) ≤ bSeq ρ s := bSeq_mono ρ hρ (by omega)
  have h3 : 0 ≤ aPrimeK (s + 1) p ρ := aP_nonneg ρ hρ s hp0 hp1
  rw [bSeq_succ] at h2
  linarith

lemma PhiK_mono_k (ρ : ℝ) (hρ : 0 < ρ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    {r s : ℕ} (hrs : r ≤ s) : PhiK r p ρ ≤ PhiK s p ρ := by
  rcases eq_or_lt_of_le hrs with rfl | h
  · exact le_rfl
  · exact (PhiK_strictMono_k ρ hρ hp0 hp1 h).le

lemma PhiK_ge_one (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    1 ≤ PhiK k p ρ := by
  unfold PhiK
  linarith [bSeq_ge_one ρ hρ k, aP_nonneg ρ hρ k hp0 hp1]

lemma PhiKDeriv_lt_sq (k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    PhiKDeriv k p ρ < (PhiK k p ρ) ^ 2 := by
  rcases k with _ | m
  · simp only [PhiKDeriv, Finset.range_zero, Finset.sum_empty, zero_add, aSeq_zero, mul_one,
      PhiK_zero]
    have he1 : 1 ≤ Real.exp (p * ρ) := Real.one_le_exp (by positivity)
    have hepos : 0 < Real.exp (p * ρ) := Real.exp_pos _
    nlinarith
  · unfold PhiKDeriv
    have hsum : ∑ j ∈ range (m + 1), aSeq ρ j * PhiK (m + 1 - j) p ρ ≤
        bSeq ρ m * PhiK (m + 1) p ρ := by
      unfold bSeq
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_left
        (PhiK_mono_k ρ hρ hp0 hp1 (Nat.sub_le _ _)) (aSeq_pos ρ hρ j).le
    have hlast : p * aSeq ρ (m + 1) * Real.exp (p * ρ) <
        aSeq ρ (m + 1) * PhiK (m + 1) p ρ := by
      have ha : 0 < aSeq ρ (m + 1) := aSeq_pos ρ hρ (m + 1)
      have he : 0 < Real.exp (p * ρ) := Real.exp_pos _
      have h0 : Real.exp (p * ρ) < PhiK (m + 1) p ρ := by
        rw [← PhiK_zero p ρ]
        exact PhiK_strictMono_k ρ hρ hp0 hp1 (Nat.succ_pos m)
      have hae : 0 < aSeq ρ (m + 1) * Real.exp (p * ρ) := mul_pos ha he
      calc p * aSeq ρ (m + 1) * Real.exp (p * ρ)
          ≤ 1 * aSeq ρ (m + 1) * Real.exp (p * ρ) := by nlinarith
        _ = aSeq ρ (m + 1) * Real.exp (p * ρ) := by ring
        _ < aSeq ρ (m + 1) * PhiK (m + 1) p ρ := mul_lt_mul_of_pos_left h0 ha
    have hb_le : bSeq ρ (m + 1) ≤ PhiK (m + 1) p ρ := by
      unfold PhiK
      linarith [aP_nonneg ρ hρ (m + 1) hp0 hp1]
    have hPpos : 0 < PhiK (m + 1) p ρ := lt_of_lt_of_le one_pos (PhiK_ge_one (m + 1) ρ hρ hp0 hp1)
    have hstep : (bSeq ρ m + aSeq ρ (m + 1)) * PhiK (m + 1) p ρ ≤ (PhiK (m + 1) p ρ) ^ 2 := by
      rw [← bSeq_succ, sq]
      exact mul_le_mul_of_nonneg_right hb_le hPpos.le
    linarith

lemma inv_Phi_add_strictMonoOn (x : ℝ) (hx : 0 ≤ x) :
    StrictMonoOn (fun ρ => 1 / Phi ρ x + ρ) (Ioi 0) := by
  set k := ⌊x⌋₊ with hk
  set p := x - (k : ℝ) with hp
  have hp0 : 0 ≤ p := sub_nonneg.2 (Nat.floor_le hx)
  have hp1 : p < 1 := by linarith [Nat.lt_floor_add_one x]
  have heq : (fun ρ => 1 / Phi ρ x + ρ) = fun ρ => 1 / PhiK k p ρ + ρ := by
    funext ρ
    unfold Phi PhiK Gk
    simp only [← hk, ← hp, hp1.ne, if_false]
  rw [heq]
  have hderiv : ∀ ρ ∈ Ioi (0 : ℝ),
      HasDerivAt (fun r => 1 / PhiK k p r + r)
        (-(PhiKDeriv k p ρ) / (PhiK k p ρ) ^ 2 + 1) ρ := by
    intro ρ hρ
    have hPne : PhiK k p ρ ≠ 0 :=
      (lt_of_lt_of_le one_pos (PhiK_ge_one k ρ hρ hp0 hp1)).ne'
    have hinv : HasDerivAt (fun r => 1 / PhiK k p r)
        (-(PhiKDeriv k p ρ) / (PhiK k p ρ) ^ 2) ρ := by
      simp_rw [one_div]
      exact (hasDerivAt_PhiK k p hp1.ne ρ).inv hPne
    exact hinv.add (hasDerivAt_id ρ)
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · exact fun ρ hρ => (hderiv ρ hρ).continuousAt.continuousWithinAt
  · intro ρ hρ
    rw [interior_Ioi] at hρ
    rw [(hderiv ρ hρ).deriv]
    have hPpos : 0 < (PhiK k p ρ) ^ 2 := by
      have := lt_of_lt_of_le one_pos (PhiK_ge_one k ρ hρ hp0 hp1)
      positivity
    have hlt := PhiKDeriv_lt_sq k hp0 hp1 hρ
    rw [neg_div, neg_add_eq_sub, sub_pos, div_lt_one hPpos]
    exact hlt

/-! ### Part 3: Joint continuity of `(ρ, x) ↦ Phi ρ x` on `(0, ∞) × [0, ∞)` -/

lemma continuous_aSeq (n : ℕ) : Continuous (fun ρ => aSeq ρ n) :=
  Differentiable.continuous fun ρ => (hasDerivAt_aSeq n ρ).differentiableAt

lemma continuous_bSeq (k : ℕ) : Continuous (fun ρ => bSeq ρ k) :=
  continuous_finsetSum _ fun i _ => continuous_aSeq i

lemma aPrimeK_continuousAt_prod (K : ℕ) (ρ₀ t₀ : ℝ) (ht₀ : t₀ ≠ 1) :
    ContinuousAt (fun q : ℝ × ℝ => aPrimeK K q.2 q.1) (ρ₀, t₀) := by
  have hne : (1 - t₀) ≠ 0 := sub_ne_zero.2 (Ne.symm ht₀)
  unfold aPrimeK
  have hexp : Continuous (fun q : ℝ × ℝ => Real.exp (q.2 * q.1)) :=
    Real.continuous_exp.comp (continuous_snd.mul continuous_fst)
  have hinv : ∀ n : ℕ, ContinuousAt (fun q : ℝ × ℝ => ((1 - q.2) ^ n)⁻¹) (ρ₀, t₀) := fun n =>
    (((continuousAt_const.sub continuousAt_snd).pow n).inv₀ (pow_ne_zero _ hne))
  apply ContinuousAt.add
  · exact (hexp.continuousAt.sub continuousAt_const).mul (hinv _)
  · apply ContinuousAt.mul
    · exact ((hexp.sub (continuous_snd.mul hexp)).sub continuous_const).continuousAt
    · apply tendsto_finsetSum (Ico 1 K)
      intro i _
      have hb : Continuous (fun q : ℝ × ℝ => bSeq q.1 i - bSeq q.1 (i - 1)) :=
        ((continuous_bSeq i).comp continuous_fst).sub ((continuous_bSeq (i - 1)).comp continuous_fst)
      exact hb.continuousAt.mul (hinv (K - i))

lemma Gk_continuousOn_prod (k : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Gk q.1 k q.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  rintro ⟨ρ₀, t₀⟩ ⟨hρ₀, ht₀⟩
  rcases eq_or_lt_of_le ht₀.2 with rfl | htlt
  · rw [ContinuousWithinAt, Gk_one, tendsto_iff_dist_tendsto_zero]
    have hb : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        dist (Gk q.1 k q.2) (aSeq ρ₀ (k + 1)) ≤
          Real.exp q.1 * aSeq q.1 (k + 1) * (1 - q.2) +
            dist (aSeq q.1 (k + 1)) (aSeq ρ₀ (k + 1)) := by
      rintro ⟨ρ, t⟩ ⟨hρ, ht⟩
      refine le_trans (dist_triangle (Gk ρ k t) (aSeq ρ (k + 1)) (aSeq ρ₀ (k + 1))) ?_
      gcongr
      rcases eq_or_lt_of_le ht.2 with rfl | ht'
      · rw [Gk_one, dist_self]; simp
      · simp only [Gk, ht'.ne, if_false]
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [aP_lt ρ hρ k t ht'])]
        exact aP_close ρ hρ k ht.1 ht'
    have hlim : Tendsto (fun q : ℝ × ℝ =>
        Real.exp q.1 * aSeq q.1 (k + 1) * (1 - q.2) +
          dist (aSeq q.1 (k + 1)) (aSeq ρ₀ (k + 1)))
        (𝓝[Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1] (ρ₀, 1)) (𝓝 0) := by
      have hcont : Continuous (fun q : ℝ × ℝ =>
          Real.exp q.1 * aSeq q.1 (k + 1) * (1 - q.2) +
            dist (aSeq q.1 (k + 1)) (aSeq ρ₀ (k + 1))) :=
        (((Real.continuous_exp.comp continuous_fst).mul
            ((continuous_aSeq (k + 1)).comp continuous_fst)).mul
          (continuous_const.sub continuous_snd)).add
        (((continuous_aSeq (k + 1)).comp continuous_fst).dist continuous_const)
      have h0 : Real.exp ρ₀ * aSeq ρ₀ (k + 1) * (1 - 1) +
          dist (aSeq ρ₀ (k + 1)) (aSeq ρ₀ (k + 1)) = 0 := by simp
      simpa [h0] using (hcont.tendsto (ρ₀, 1)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with q hq using hb q hq
  · have hc := aPrimeK_continuousAt_prod (k + 1) ρ₀ t₀ htlt.ne
    have heq : (fun q : ℝ × ℝ => Gk q.1 k q.2) =ᶠ[𝓝 (ρ₀, t₀)]
        (fun q : ℝ × ℝ => aPrimeK (k + 1) q.2 q.1) := by
      have hopen : IsOpen {q : ℝ × ℝ | q.2 < 1} := isOpen_lt continuous_snd continuous_const
      filter_upwards [hopen.mem_nhds htlt] with q hq
      simp [Gk, (ne_of_lt hq : q.2 ≠ 1)]
    exact (hc.congr heq.symm).continuousWithinAt

lemma Phi_continuousOn_strip (k : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Phi q.1 q.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (k : ℝ) (k + 1)) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => bSeq q.1 k + Gk q.1 k (q.2 - k))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (k : ℝ) (k + 1)) := by
    apply ((continuous_bSeq k).comp continuous_fst).continuousOn.add
    have hmap : ContinuousOn (fun q : ℝ × ℝ => (q.1, q.2 - (k : ℝ)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (k : ℝ) (k + 1)) :=
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
    refine (Gk_continuousOn_prod k).comp hmap ?_
    rintro ⟨ρ, x⟩ ⟨hρ, hx⟩
    exact ⟨hρ, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
  exact h1.congr fun q hq => Phi_eq q.1 k q.2 hq.2

lemma Phi_continuousOn_prod :
    ContinuousOn (fun q : ℝ × ℝ => Phi q.1 q.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
  rintro ⟨ρ₀, x₀⟩ ⟨hρ₀, hx₀⟩
  set k := ⌊x₀⌋₊
  have hk1 : (k : ℝ) ≤ x₀ := Nat.floor_le hx₀
  have hk2 : x₀ < k + 1 := Nat.lt_floor_add_one x₀
  rcases eq_or_lt_of_le hk1 with h | h
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hx0 : x₀ = 0 := by rw [← h, hk0]; simp
      have h1 := Phi_continuousOn_strip 0 (ρ₀, x₀) ⟨hρ₀, by rw [hx0]; simp⟩
      apply h1.mono_of_mem_nhdsWithin
      rw [mem_nhdsWithin]
      refine ⟨Set.Ioi (0 : ℝ) ×ˢ Set.Iio (1 : ℝ), isOpen_Ioi.prod isOpen_Iio,
        ⟨hρ₀, by rw [hx0]; norm_num⟩, ?_⟩
      rintro ⟨ρ, x⟩ ⟨⟨hρ', hxlt⟩, ⟨_, hxge⟩⟩
      exact ⟨hρ', by simpa using ⟨hxge, hxlt.le⟩⟩
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hmem_j : (ρ₀, x₀) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Icc (j : ℝ) (j + 1) := by
        refine ⟨hρ₀, ?_, ?_⟩ <;> rw [← h, hj] <;> push_cast <;> linarith
      have h1 := Phi_continuousOn_strip j (ρ₀, x₀) hmem_j
      have h2 := Phi_continuousOn_strip k (ρ₀, x₀) ⟨hρ₀, hk1, hk2.le⟩
      have h3 := h1.union h2
      apply h3.mono_of_mem_nhdsWithin
      apply mem_nhdsWithin_of_mem_nhds
      have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Icc (j : ℝ) (k + 1) ⊆
          Set.Ioi (0 : ℝ) ×ˢ Set.Icc (j : ℝ) (j + 1) ∪
            Set.Ioi (0 : ℝ) ×ˢ Set.Icc (k : ℝ) (k + 1) := by
        rintro ⟨ρ, x⟩ ⟨hρ', hx⟩
        by_cases hxk : x ≤ k
        · left; rw [hj] at hxk; push_cast at hxk; exact ⟨hρ', hx.1, hxk⟩
        · right; push Not at hxk; exact ⟨hρ', hxk.le, hx.2⟩
      apply Filter.mem_of_superset _ hsub
      exact prod_mem_nhds (isOpen_Ioi.mem_nhds hρ₀)
        (Icc_mem_nhds (by rw [← h, hj]; push_cast; linarith) hk2)
  · have h2 := Phi_continuousOn_strip k (ρ₀, x₀) ⟨hρ₀, hk1, hk2.le⟩
    have hnhds : Set.Ioi (0 : ℝ) ×ˢ Set.Icc (k : ℝ) (k + 1) ∈ 𝓝 (ρ₀, x₀) :=
      prod_mem_nhds (isOpen_Ioi.mem_nhds hρ₀) (Icc_mem_nhds h hk2)
    exact (h2.continuousAt hnhds).continuousWithinAt

/-! ### Part 4: Main theorem -/

theorem main (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 ≤ δ) :
    StrictAntiOn (fun μS => OutpatientWalkIn.Triage.blockProb lam δ μS) (Set.Ioi 0) ∧
      ContinuousOn (fun μS => OutpatientWalkIn.Triage.blockProb lam δ μS) (Set.Ioi 0) := by
  have heq : EqOn (fun μS => OutpatientWalkIn.Triage.blockProb lam δ μS)
      (fun μS => 1 - 1 / (1 / Phi (lam / μS) (δ * μS) + lam / μS)) (Set.Ioi 0) :=
    fun μS hμS => triage_blockProb_eq lam δ μS hδ hμS
  constructor
  · intro μ1 hμ1 μ2 hμ2 hlt
    rw [heq hμ1, heq hμ2]
    set ρ1 := lam / μ1
    set ρ2 := lam / μ2
    set x1 := δ * μ1
    set x2 := δ * μ2
    have hρ1 : 0 < ρ1 := div_pos hlam hμ1
    have hρ2 : 0 < ρ2 := div_pos hlam hμ2
    have hρlt : ρ2 < ρ1 := div_lt_div_of_pos_left hlam hμ1 hlt
    have hx1 : 0 ≤ x1 := mul_nonneg hδ (le_of_lt hμ1)
    have hx2 : 0 ≤ x2 := mul_nonneg hδ (le_of_lt hμ2)
    have hxle : x1 ≤ x2 := mul_le_mul_of_nonneg_left hlt.le hδ
    have hP1 : 0 < Phi ρ2 x1 := lt_of_lt_of_le one_pos (Phi_ge_one ρ2 hρ2 x1 hx1)
    have hP2 : 0 < Phi ρ2 x2 := lt_of_lt_of_le one_pos (Phi_ge_one ρ2 hρ2 x2 hx2)
    have hPle : Phi ρ2 x1 ≤ Phi ρ2 x2 := (Phi_strictMonoOn ρ2 hρ2).monotoneOn hx1 hx2 hxle
    have hinv_le : 1 / Phi ρ2 x2 ≤ 1 / Phi ρ2 x1 := one_div_le_one_div_of_le hP1 hPle
    have hmono := inv_Phi_add_strictMonoOn x1 hx1 hρ2 hρ1 hρlt
    have hden_pos : 0 < 1 / Phi ρ2 x2 + ρ2 := by positivity
    have hden_lt : 1 / Phi ρ2 x2 + ρ2 < 1 / Phi ρ1 x1 + ρ1 := by linarith
    have hrec_lt : 1 / (1 / Phi ρ1 x1 + ρ1) < 1 / (1 / Phi ρ2 x2 + ρ2) :=
      one_div_lt_one_div_of_lt hden_pos hden_lt
    linarith
  · refine ContinuousOn.congr ?_ heq
    have hmap : ContinuousOn (fun μS : ℝ => (lam / μS, δ * μS)) (Set.Ioi 0) :=
      (continuousOn_const.div continuousOn_id (fun μS hμS => (ne_of_gt hμS))).prodMk
        (continuousOn_const.mul continuousOn_id)
    have hPhi : ContinuousOn (fun μS : ℝ => Phi (lam / μS) (δ * μS)) (Set.Ioi 0) := by
      change ContinuousOn ((fun q : ℝ × ℝ => Phi q.1 q.2) ∘ fun μS : ℝ => (lam / μS, δ * μS))
        (Set.Ioi 0)
      refine Phi_continuousOn_prod.comp hmap ?_
      intro μS hμS
      exact ⟨div_pos hlam hμS, mul_nonneg hδ (le_of_lt hμS)⟩
    have hPne : ∀ μS ∈ Set.Ioi (0 : ℝ), Phi (lam / μS) (δ * μS) ≠ 0 := fun μS hμS =>
      (lt_of_lt_of_le one_pos
        (Phi_ge_one (lam / μS) (div_pos hlam hμS) (δ * μS) (mul_nonneg hδ (le_of_lt hμS)))).ne'
    have hden : ContinuousOn (fun μS : ℝ => 1 / Phi (lam / μS) (δ * μS) + lam / μS) (Set.Ioi 0) :=
      (continuousOn_const.div hPhi hPne).add
        (continuousOn_const.div continuousOn_id (fun μS hμS => (ne_of_gt hμS)))
    refine continuousOn_const.sub (continuousOn_const.div hden fun μS hμS => ?_)
    have hPpos : 0 < Phi (lam / μS) (δ * μS) := lt_of_lt_of_le one_pos
      (Phi_ge_one (lam / μS) (div_pos hlam hμS) (δ * μS) (mul_nonneg hδ (le_of_lt hμS)))
    have hρpos : 0 < lam / μS := div_pos hlam hμS
    positivity

end OWTriageC2

open OutpatientWalkIn.Triage

theorem solution (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 ≤ δ) :
    StrictAntiOn (fun μS => blockProb lam δ μS) (Set.Ioi 0) ∧
      ContinuousOn (fun μS => blockProb lam δ μS) (Set.Ioi 0) :=
  OWTriageC2.main lam δ hlam hδ
