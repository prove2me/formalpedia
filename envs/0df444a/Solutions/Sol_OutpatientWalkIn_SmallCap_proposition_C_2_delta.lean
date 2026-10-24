-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.proposition_C_2_delta
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:05:55.743837+00:00
-- url     : https://prove2.me/submissions/be031685-fbd9-4622-98e9-7196ace6e547

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue


namespace OWSCQ

open OutpatientWalkIn.SmallCap Finset

theorem aSeq_zero (ρ : ℝ) : aSeq ρ 0 = 1 := by rw [aSeq]

theorem aSeq_succ (ρ : ℝ) (n : ℕ) : aSeq ρ (n + 1) = Real.exp ρ *
    (aSeq ρ n - ∑ i ∈ Ico 1 (n + 1), alphaP ρ i * aSeq ρ (n + 1 - i) - alphaP ρ n) := by
  rw [aSeq, aSeq_zero, mul_one]
  congr 2
  rw [Finset.sum_attach (Ico 1 (n + 1)) (fun i => alphaP ρ i * aSeq ρ (n + 1 - i))]
  -- (Ico 1 (n + 1)) (fun i => alphaP ρ i * aSeq ρ (n + 1 - i))

theorem aSeq_one (ρ : ℝ) : aSeq ρ 1 = Real.exp ρ - 1 := by
  rw [aSeq_succ, aSeq_zero]
  simp [alphaP]
  rw [mul_sub, mul_one, ← Real.exp_add]; simp

/-- the recursion in "level" form -/
theorem aSeq_rec (ρ : ℝ) (k : ℕ) :
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
      intro i hi
      rw [show 1 + i = i + 1 by ring, show k + 1 + 1 - (i + 1) = k + 1 - i by omega]
    · rw [show 1 + k = k + 1 by ring, show k + 1 + 1 - (k + 1) = 1 by omega]
  rw [hsplit, aSeq_one] at h
  have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
  rw [ha0]
  rw [h]
  have : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
  linear_combination (aSeq ρ (k + 1) - (∑ i ∈ range k, alphaP ρ (i + 1) * aSeq ρ (k + 1 - i) +
      alphaP ρ (k + 1) * (Real.exp ρ - 1)) - alphaP ρ (k + 1)) * this

theorem bSeq_sub (ρ : ℝ) (i : ℕ) (hi : 1 ≤ i) : bSeq ρ i - bSeq ρ (i - 1) = aSeq ρ i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [bSeq, Finset.sum_range_succ]

theorem bSeq_succ (ρ : ℝ) (k : ℕ) : bSeq ρ (k + 1) = bSeq ρ k + aSeq ρ (k + 1) := by
  simp [bSeq, Finset.sum_range_succ]

/-- `Q_i(x) = (e^x - Σ_{m ≤ i} x^m/m!)/x^{i+1}` -/
noncomputable def Qf (i : ℕ) (x : ℝ) : ℝ :=
  (Real.exp x - ∑ m ∈ range (i + 1), x ^ m / (m.factorial : ℝ)) / x ^ (i + 1)

theorem Qf_succ (i : ℕ) (x : ℝ) (hx : x ≠ 0) :
    x * Qf (i + 1) x = Qf i x - 1 / ((i + 1).factorial : ℝ) := by
  unfold Qf
  rw [Finset.sum_range_succ (n := i + 1)]
  have hf : ((i + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem Qf_zero (x : ℝ) (hx : x ≠ 0) : x * Qf 0 x = Real.exp x - 1 := by
  unfold Qf; simp; field_simp

theorem Qf_hasSum (i : ℕ) (x : ℝ) (hx : 0 < x) :
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

theorem Qf_pos (i : ℕ) (x : ℝ) (hx : 0 < x) : 0 < Qf i x := by
  have h := Qf_hasSum i x hx
  have : (0:ℝ) < 1 / ((0 + i + 1).factorial : ℝ) := by positivity
  refine lt_of_lt_of_le this ?_
  have := h.nonneg (fun n => by positivity)
  have h0 := (sum_le_hasSum (Finset.range 1) (fun n _ => by positivity) h)
  simpa using h0

theorem Qf_strictMono (i : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) : Qf i x < Qf i y := by
  have hy : 0 < y := lt_trans hx hxy
  refine hasSum_lt (f := fun n : ℕ => x ^ n / ((n + i + 1).factorial : ℝ))
    (g := fun n : ℕ => y ^ n / ((n + i + 1).factorial : ℝ)) (i := 1) ?_ ?_
    (Qf_hasSum i x hx) (Qf_hasSum i y hy)
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hx.le hxy.le n
  · simp only [pow_one]
    exact div_lt_div_of_pos_right hxy (by positivity)

end OWSCQ


namespace OWSCQ

open OutpatientWalkIn.SmallCap Finset

theorem aP_one (p ρ : ℝ) : aPrimeK 1 p ρ = Real.exp (p * ρ) - 1 := by
  simp [aPrimeK]

theorem aP_rec (k : ℕ) (p ρ : ℝ) (hp : p ≠ 1) :
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
    show k + 1 + 1 - (k + 1) = 1 by omega, pow_one, pow_succ]
  field_simp
  ring

/-- `H_{k+1}(s) = Γ_{k+1}(s)/s` -/
noncomputable def Hh (ρ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ range k, aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) * Qf i (ρ * s)
    + ρ ^ (k + 1) * Qf k (ρ * s)

theorem Hh_key (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (s : ℝ) (hs : s ≠ 0) :
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
    have : s * (aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) (ρ * s)) =
        aSeq ρ (k + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1) * ((ρ * s) * Qf (i + 1) (ρ * s)) := by
      ring
    rw [this, h1]
    simp only [alphaP]
    push_cast
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
    have : s * (ρ ^ (k + 1 + 1) * Qf (k + 1) (ρ * s)) = ρ ^ (k + 1) * ((ρ * s) * Qf (k + 1) (ρ * s)) := by
      ring
    rw [this, h1]; ring
  rw [mul_add, mul_add, hsum, h0, hlast]
  have ha0 : alphaP ρ 0 = Real.exp (-ρ) := by simp [alphaP]
  have hak : Real.exp ρ * alphaP ρ (k + 1) = ρ ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    simp only [alphaP]
    have : Real.exp ρ * Real.exp (-ρ) = 1 := by rw [← Real.exp_add]; simp
    rw [← mul_div_assoc, ← mul_assoc, this, one_mul]
  rw [ha0, hak] at hrec
  linear_combination -hrec

theorem aP_eq (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
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
    have : Real.exp (p * ρ) * (1 - p) * (ρ * Qf 0 (ρ * (1 - p))) =
        Real.exp (p * ρ) * (ρ * (1 - p) * Qf 0 (ρ * (1 - p))) := by ring
    rw [this, h]
    linear_combination hee
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by ring, aP_rec k p ρ (by linarith), ih]
    have hkey := Hh_key ρ hρ k (1 - p) hs
    rw [div_eq_iff hs]
    linear_combination (Real.exp (p * ρ) * (1 - p)) * hkey + ((1 - p) * aSeq ρ (k + 2)) * hee'

end OWSCQ


namespace OWSCQ

open OutpatientWalkIn.SmallCap Finset

theorem aP_zero (k : ℕ) (ρ : ℝ) : aPrimeK (k + 1) 0 ρ = 0 := by
  simp [aPrimeK]

theorem a_eq_Hh (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : aSeq ρ (k + 1) = Hh ρ k 1 := by
  have h := aP_eq ρ hρ k 0 (by norm_num)
  rw [aP_zero] at h
  simp at h
  linarith

theorem aSeq_pos (ρ : ℝ) (hρ : 0 < ρ) : ∀ n, 0 < aSeq ρ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · rw [aSeq_zero]; norm_num
    rw [a_eq_Hh ρ hρ k]
    rcases k with _ | m
    · unfold Hh; simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact mul_pos (by positivity) (Qf_pos 0 _ (by positivity))
    · -- split off the i = 0 term which contains a_{m+2} itself
      have hsplit : Hh ρ (m + 1) 1 = aSeq ρ (m + 2) * (1 - Real.exp (-ρ)) +
          (∑ i ∈ range m, aSeq ρ (m + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) ρ
            + ρ ^ (m + 1 + 1) * Qf (m + 1) ρ) := by
        unfold Hh
        rw [Finset.sum_range_succ']
        have hq := Qf_zero ρ hρ.ne'
        simp only [mul_one, show m + 1 + 1 - 0 = m + 2 by omega, zero_add, pow_one]
        have : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
        have e2 : ∀ i ∈ range m, aSeq ρ (m + 1 + 1 - (i + 1)) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) *
            Qf (i + 1) ρ = aSeq ρ (m + 1 - i) * Real.exp (-ρ) * ρ ^ (i + 1 + 1) * Qf (i + 1) ρ := by
          intro i _; rw [show m + 1 + 1 - (i + 1) = m + 1 - i by omega]
        rw [Finset.sum_congr rfl e2]
        linear_combination (aSeq ρ (m + 2) * Real.exp (-ρ)) * hq + aSeq ρ (m + 2) * this
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

theorem Hh_pos (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (s : ℝ) (hs : 0 < s) : 0 < Hh ρ k s := by
  unfold Hh
  apply add_pos_of_nonneg_of_pos
  · apply Finset.sum_nonneg
    intro i _
    have := aSeq_pos ρ hρ (k + 1 - i)
    have := Qf_pos i (ρ * s) (by positivity)
    positivity
  · exact mul_pos (by positivity) (Qf_pos _ _ (by positivity))

theorem Hh_strictMono (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
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

theorem Hh_le (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Hh ρ k s ≤ aSeq ρ (k + 1) := by
  rw [a_eq_Hh ρ hρ k]
  rcases eq_or_lt_of_le hs1 with h | h
  · rw [h]
  · exact (Hh_strictMono ρ hρ k hs h).le

/-- recursion form `a'_{k+2}(p) = e^{pρ} (a_{k+1} - H_{k+1}(1-p))` -/
theorem aP_succ_form (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
    aPrimeK (k + 2) p ρ = Real.exp (p * ρ) * (aSeq ρ (k + 1) - Hh ρ k (1 - p)) := by
  have hs : (1 - p) ≠ 0 := by linarith
  rw [aP_rec k p ρ (by linarith), aP_eq ρ hρ k p hp, div_eq_iff hs]
  ring

theorem aP_lt (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (p : ℝ) (hp : p < 1) :
    aPrimeK (k + 1) p ρ < aSeq ρ (k + 1) := by
  rw [aP_eq ρ hρ k p hp]
  have := Hh_pos ρ hρ k (1 - p) (by linarith)
  have : 0 < 1 - p := by linarith
  have : 0 < Real.exp (p * ρ) * (1 - p) * Hh ρ k (1 - p) := by positivity
  linarith

theorem aP_strictMono (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q)
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

theorem aP_nonneg (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    0 ≤ aPrimeK (k + 1) p ρ := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h, aP_zero]
  · rw [← aP_zero k ρ]; exact (aP_strictMono ρ hρ k le_rfl h hp1).le

theorem aP_close (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    aSeq ρ (k + 1) - aPrimeK (k + 1) p ρ ≤ Real.exp ρ * aSeq ρ (k + 1) * (1 - p) := by
  rw [aP_eq ρ hρ k p hp1]
  have h1 := Hh_le ρ hρ k (s := 1 - p) (by linarith) (by linarith)
  have h2 : Real.exp (p * ρ) ≤ Real.exp ρ := Real.exp_le_exp.2 (by nlinarith)
  have h3 := Hh_pos ρ hρ k (1 - p) (by linarith)
  have h4 : 0 ≤ 1 - p := by linarith
  have : Real.exp (p * ρ) * (1 - p) * Hh ρ k (1 - p) ≤ Real.exp ρ * (1 - p) * aSeq ρ (k + 1) := by
    apply mul_le_mul _ h1 h3.le (by positivity)
    exact mul_le_mul_of_nonneg_right h2 h4
  linarith

end OWSCQ


namespace OWSCQ

open OutpatientWalkIn.SmallCap Finset Set Filter Topology

noncomputable def Gk (ρ : ℝ) (k : ℕ) (t : ℝ) : ℝ := if t = 1 then aSeq ρ (k + 1) else aPrimeK (k + 1) t ρ

theorem Gk_zero (ρ : ℝ) (k : ℕ) : Gk ρ k 0 = 0 := by
  simp [Gk, aP_zero]

theorem Gk_one (ρ : ℝ) (k : ℕ) : Gk ρ k 1 = aSeq ρ (k + 1) := by simp [Gk]

theorem Gk_strictMonoOn (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : StrictMonoOn (Gk ρ k) (Icc 0 1) := by
  intro t ht t' ht' htt
  have ht1 : t ≠ 1 := by intro h; rw [h] at htt; linarith [ht'.2]
  rcases eq_or_lt_of_le ht'.2 with h | h
  · rw [h, Gk_one]; simp only [Gk, ht1, if_false]
    exact aP_lt ρ hρ k t (by rw [← h]; exact htt)
  · simp only [Gk, ht1, h.ne, if_false]
    exact aP_strictMono ρ hρ k ht.1 htt h

theorem aP_continuousAt (ρ : ℝ) (K : ℕ) (t : ℝ) (ht : t ≠ 1) :
    ContinuousAt (fun t => aPrimeK K t ρ) t := by
  have hne : (1 - t) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  unfold aPrimeK
  have hinv : ∀ n : ℕ, ContinuousAt (fun t : ℝ => ((1 - t) ^ n)⁻¹) t := fun n =>
    ((continuousAt_const.sub continuousAt_id).pow n).inv₀ (pow_ne_zero _ hne)
  apply ContinuousAt.add
  · exact ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousAt.sub
      continuousAt_const).mul (hinv _)
  · apply ContinuousAt.mul
    · have he : Continuous fun t : ℝ => Real.exp (t * ρ) :=
        Real.continuous_exp.comp (continuous_id.mul continuous_const)
      exact ((he.sub (continuous_id.mul he)).sub continuous_const).continuousAt
    · exact tendsto_finsetSum (Ico 1 K) (fun i _ => (continuousAt_const.mul (hinv (K - i)) :
        ContinuousAt (fun t : ℝ => (bSeq ρ i - bSeq ρ (i - 1)) * ((1 - t) ^ (K - i))⁻¹) t))

theorem Gk_continuousOn (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : ContinuousOn (Gk ρ k) (Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with h | h
  · -- t = 1 : squeeze
    rw [h]
    rw [ContinuousWithinAt, Gk_one]
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : ∀ u ∈ Icc (0:ℝ) 1, dist (Gk ρ k u) (aSeq ρ (k + 1)) ≤
        Real.exp ρ * aSeq ρ (k + 1) * (1 - u) := by
      intro u hu
      rcases eq_or_lt_of_le hu.2 with h' | h'
      · rw [h', Gk_one]; simp
      · simp only [Gk, h'.ne, if_false]
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [aP_lt ρ hρ k u h'])]
        exact aP_close ρ hρ k hu.1 h'
    have hlim : Tendsto (fun u : ℝ => Real.exp ρ * aSeq ρ (k + 1) * (1 - u)) (𝓝[Icc 0 1] 1) (𝓝 0) := by
      have : Tendsto (fun u : ℝ => Real.exp ρ * aSeq ρ (k + 1) * (1 - u)) (𝓝 1)
          (𝓝 (Real.exp ρ * aSeq ρ (k + 1) * (1 - 1))) :=
        ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1)
      rw [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    apply squeeze_zero' (Eventually.of_forall (fun u => dist_nonneg)) _ hlim
    filter_upwards [self_mem_nhdsWithin] with u hu using hb u hu
  · -- t < 1
    have hc := aP_continuousAt ρ (k + 1) t h.ne
    have heq : Gk ρ k =ᶠ[𝓝 t] (fun t => aPrimeK (k + 1) t ρ) := by
      filter_upwards [Iio_mem_nhds h] with u hu
      simp [Gk, (show u ≠ 1 from (ne_of_lt hu))]
    exact (hc.congr heq.symm).continuousWithinAt

/-- the reciprocal of `q_0` as a function of the buffer `x = δ μ_S` -/
noncomputable def Phi (ρ : ℝ) (x : ℝ) : ℝ := bSeq ρ ⌊x⌋₊ + Gk ρ ⌊x⌋₊ (x - ⌊x⌋₊)

theorem Phi_eq (ρ : ℝ) (k : ℕ) (x : ℝ) (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    Phi ρ x = bSeq ρ k + Gk ρ k (x - k) := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hf : ⌊x⌋₊ = k + 1 := by rw [h]; exact_mod_cast Nat.floor_natCast (R := ℝ) (k + 1)
    unfold Phi
    rw [hf, h]; push_cast
    rw [sub_self, Gk_zero, show (k : ℝ) + 1 - k = 1 by ring, Gk_one, bSeq_succ]; ring
  · have hf : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)])]
      exact ⟨hx.1, h⟩
    unfold Phi; rw [hf]

theorem q0_eq (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) (hx : 0 ≤ x) :
    q0 ⌈x⌉₊ (x + 1 - ⌈x⌉₊) ρ = 1 / Phi ρ x := by
  set k := ⌊x⌋₊ with hk
  have hk1 : (k : ℝ) ≤ x := Nat.floor_le hx
  have hk2 : x < k + 1 := Nat.lt_floor_add_one x
  rcases eq_or_lt_of_le hk1 with h | h
  · -- x = k
    have hc : ⌈x⌉₊ = k := by rw [← h]; exact Nat.ceil_natCast k
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

theorem Phi_ge (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (x : ℝ) (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    bSeq ρ k ≤ Phi ρ x ∧ Phi ρ x ≤ bSeq ρ (k + 1) := by
  rw [Phi_eq ρ k x hx]
  have ht : x - k ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hm := Gk_strictMonoOn ρ hρ k
  have h0 : Gk ρ k 0 ≤ Gk ρ k (x - k) := hm.monotoneOn ⟨le_rfl, zero_le_one⟩ ht ht.1
  have h1 : Gk ρ k (x - k) ≤ Gk ρ k 1 := hm.monotoneOn ht ⟨zero_le_one, le_rfl⟩ ht.2
  rw [Gk_zero] at h0; rw [Gk_one] at h1
  rw [bSeq_succ]
  constructor <;> linarith

theorem bSeq_ge_one (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) : 1 ≤ bSeq ρ k := by
  induction k with
  | zero => simp [bSeq, aSeq_zero]
  | succ k ih => rw [bSeq_succ]; linarith [aSeq_pos ρ hρ (k + 1)]

theorem Phi_ge_one (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ Phi ρ x := by
  have := (Phi_ge ρ hρ ⌊x⌋₊ x ⟨Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩).1
  linarith [bSeq_ge_one ρ hρ ⌊x⌋₊]

theorem Phi_continuousOn_piece (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    ContinuousOn (Phi ρ) (Icc (k : ℝ) (k + 1)) := by
  have hG := Gk_continuousOn ρ hρ k
  have : ContinuousOn (fun x => bSeq ρ k + Gk ρ k (x - k)) (Icc (k : ℝ) (k + 1)) := by
    apply continuousOn_const.add
    apply hG.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    have h1 := hx.1; have h2 := hx.2
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  exact this.congr (fun x hx => Phi_eq ρ k x hx)

theorem Phi_strictMonoOn_piece (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    StrictMonoOn (Phi ρ) (Icc (k : ℝ) (k + 1)) := by
  intro x hx y hy hxy
  rw [Phi_eq ρ k x hx, Phi_eq ρ k y hy]
  have := Gk_strictMonoOn ρ hρ k ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith : x - k < y - k)
  linarith

/-- gluing: continuity on every unit interval gives continuity on `[0,∞)` -/
theorem continuousOn_glue (f : ℝ → ℝ) (hf : ∀ k : ℕ, ContinuousOn f (Icc (k : ℝ) (k + 1))) :
    ContinuousOn f (Ici 0) := by
  intro x hx
  have hx0 : (0:ℝ) ≤ x := hx
  set k := ⌊x⌋₊
  have hk1 : (k : ℝ) ≤ x := Nat.floor_le hx0
  have hk2 : x < k + 1 := Nat.lt_floor_add_one x
  rcases eq_or_lt_of_le hk1 with h | h
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · -- x = 0
      have hx' : x = 0 := by rw [← h, hk0]; simp
      have h1 := hf 0 x (by rw [hx']; simp)
      apply h1.mono_of_mem_nhdsWithin
      rw [mem_nhdsWithin]
      refine ⟨Iio 1, isOpen_Iio, by rw [hx']; simp, ?_⟩
      intro y ⟨hy1, hy2⟩
      simp only [Nat.cast_zero, zero_add]
      exact ⟨hy2, (le_of_lt hy1)⟩
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h1 := hf j x (by rw [← h, hj]; push_cast; constructor <;> linarith)
      have h2 := hf k x ⟨hk1, hk2.le⟩
      have h3 := h1.union h2
      apply h3.mono_of_mem_nhdsWithin
      apply mem_nhdsWithin_of_mem_nhds
      have : Icc ((j : ℝ)) (k + 1) ⊆ Icc (j : ℝ) (j + 1) ∪ Icc (k : ℝ) (k + 1) := by
        intro y hy
        by_cases hyk : y ≤ k
        · left; rw [hj] at hyk; push_cast at hyk; exact ⟨hy.1, hyk⟩
        · right; push Not at hyk; exact ⟨hyk.le, hy.2⟩
      apply Filter.mem_of_superset _ this
      apply Icc_mem_nhds
      · rw [← h, hj]; push_cast; linarith
      · linarith
  · have h2 := hf k x ⟨hk1, hk2.le⟩
    exact (h2.continuousAt (Icc_mem_nhds h hk2)).continuousWithinAt

theorem strictMonoOn_glue (f : ℝ → ℝ) (hf : ∀ k : ℕ, StrictMonoOn f (Icc (k : ℝ) (k + 1))) :
    StrictMonoOn f (Ici 0) := by
  have key : ∀ m : ℕ, ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ m → f x < f y := by
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
      · exact hf m ⟨hxm, by linarith⟩ ⟨by linarith, hy⟩ hxy
      push Not at hxm
      have h1 := ih x m hx hxm le_rfl
      have h2 := hf m ⟨le_rfl, by linarith⟩ ⟨hym.le, hy⟩ hym
      linarith
  intro x hx y hy hxy
  exact key ⌈y⌉₊ x y hx hxy (Nat.le_ceil y)

theorem Phi_continuousOn (ρ : ℝ) (hρ : 0 < ρ) : ContinuousOn (Phi ρ) (Ici 0) :=
  continuousOn_glue _ (Phi_continuousOn_piece ρ hρ)

theorem Phi_strictMonoOn (ρ : ℝ) (hρ : 0 < ρ) : StrictMonoOn (Phi ρ) (Ici 0) :=
  strictMonoOn_glue _ (Phi_strictMonoOn_piece ρ hρ)

end OWSCQ


namespace OWSCQ

open OutpatientWalkIn.SmallCap Finset

/-- exponential remainder `R_j(x) = x^{j+1} Q_j(x) = e^x - Σ_{m ≤ j} x^m/m!` -/
noncomputable def Rr (x : ℝ) (j : ℕ) : ℝ := x ^ (j + 1) * Qf j x

theorem Rr_zero (x : ℝ) (hx : x ≠ 0) : Rr x 0 = Real.exp x - 1 := by
  unfold Rr; rw [zero_add, pow_one, Qf_zero x hx]

theorem Rr_succ (x : ℝ) (hx : x ≠ 0) (j : ℕ) :
    Rr x (j + 1) = Rr x j - x ^ (j + 1) / ((j + 1).factorial : ℝ) := by
  unfold Rr
  have h := Qf_succ j x hx
  have : x ^ (j + 1 + 1) * Qf (j + 1) x = x ^ (j + 1) * (x * Qf (j + 1) x) := by ring
  rw [this, h]; ring

theorem Rr_sum (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ∑ j ∈ range (n + 1), Rr x j = x * Real.exp x - x * Rr x n + (n + 1) * Rr x (n + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, one_mul]
    rw [Rr_succ x hx 0, Rr_zero x hx]; simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Rr_succ x hx (n + 1), Rr_succ x hx n]
    have hf : ((n + 1 + 1).factorial : ℝ) = (n + 2) * ((n + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf0 : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [hf]; push_cast
    field_simp
    ring

theorem Qf_ratio (n : ℕ) (x : ℝ) (hx : 0 < x) : (n + 1) * Qf (n + 1) x ≤ Qf n x := by
  have h1 := (Qf_hasSum (n + 1) x hx).mul_left ((n : ℝ) + 1)
  have h2 := Qf_hasSum n x hx
  refine hasSum_le (fun m => ?_) h1 h2
  have hf : ((m + (n + 1) + 1).factorial : ℝ) = (m + n + 2) * ((m + n + 1).factorial : ℝ) := by
    rw [show m + (n + 1) + 1 = (m + n + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  rw [hf]
  have hpos : (0:ℝ) < ((m + n + 1).factorial : ℝ) := by positivity
  have hxm : 0 ≤ x ^ m := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hpos]
  have : ((n:ℝ) + 1) * x ^ m * ((m + n + 1).factorial : ℝ) ≤
      x ^ m * ((m + n + 2) * ((m + n + 1).factorial : ℝ)) := by
    have : ((n:ℝ) + 1) ≤ (m + n + 2) := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    nlinarith [mul_nonneg hxm hpos.le]
  linarith

theorem Rr_sum_le (x : ℝ) (hx : 0 < x) (n : ℕ) : ∑ j ∈ range n, Rr x j ≤ x * Real.exp x := by
  rcases n with _ | n
  · simp; positivity
  rw [Rr_sum x hx.ne' n]
  have h := Qf_ratio n x hx
  have : (n + 1) * Rr x (n + 1) ≤ x * Rr x n := by
    unfold Rr
    have e1 : ((n:ℝ) + 1) * (x ^ (n + 1 + 1) * Qf (n + 1) x) = x ^ (n + 2) * ((n + 1) * Qf (n + 1) x) := by
      ring
    have e2 : x * (x ^ (n + 1) * Qf n x) = x ^ (n + 2) * Qf n x := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  push_cast at this ⊢
  linarith

noncomputable def Abar (ρ : ℝ) (i : ℕ) : ℝ := Real.exp (-ρ) * Rr ρ i

theorem Abar_nonneg (ρ : ℝ) (hρ : 0 < ρ) (i : ℕ) : 0 ≤ Abar ρ i := by
  unfold Abar Rr; have := Qf_pos i ρ hρ; positivity

theorem Abar_sum_le (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) : ∑ i ∈ range n, Abar ρ i ≤ ρ := by
  unfold Abar
  rw [← Finset.mul_sum]
  have h := Rr_sum_le ρ hρ n
  have he : Real.exp (-ρ) * Real.exp ρ = 1 := by rw [← Real.exp_add]; simp
  have : Real.exp (-ρ) * ∑ i ∈ range n, Rr ρ i ≤ Real.exp (-ρ) * (ρ * Real.exp ρ) :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  nlinarith

theorem a_level (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    aSeq ρ (k + 1) = ∑ i ∈ range k, aSeq ρ (k + 1 - i) * Abar ρ i + Real.exp ρ * Abar ρ k := by
  rw [a_eq_Hh ρ hρ k]
  unfold Hh Abar Rr
  simp only [mul_one]
  have he : Real.exp ρ * Real.exp (-ρ) = 1 := by rw [← Real.exp_add]; simp
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · linear_combination (-(ρ ^ (k + 1) * Qf k ρ)) * he

theorem double_sum_eq (f : ℕ → ℝ) (g : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ range M, ∑ i ∈ range k, f (k + 1 - i) * g i =
      ∑ i ∈ range M, g i * ∑ j ∈ range (M - 1 - i), f (j + 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [show M + 1 - 1 - M = 0 by omega, Finset.range_zero, Finset.sum_empty, mul_zero,
      add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show M + 1 - 1 - i = (M - 1 - i) + 1 by omega, Finset.sum_range_succ,
      show M - 1 - i + 2 = M + 1 - i by omega]
    ring

theorem bSeq_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (M : ℕ) : bSeq ρ M * (1 - ρ) ≤ 1 := by
  rcases M with _ | m
  · simp [bSeq, aSeq_zero]; linarith
  have hb : bSeq ρ (m + 1) = 1 + ∑ k ∈ range (m + 1), aSeq ρ (k + 1) := by
    unfold bSeq; rw [Finset.sum_range_succ', aSeq_zero]; ring
  have hb2 : bSeq ρ (m + 1) = 1 + (Real.exp ρ - 1) + ∑ j ∈ range m, aSeq ρ (j + 2) := by
    unfold bSeq; rw [Finset.sum_range_succ', Finset.sum_range_succ', aSeq_zero, aSeq_one]; ring
  have hlev : ∑ k ∈ range (m + 1), aSeq ρ (k + 1) =
      ∑ k ∈ range (m + 1), ∑ i ∈ range k, aSeq ρ (k + 1 - i) * Abar ρ i +
        Real.exp ρ * ∑ k ∈ range (m + 1), Abar ρ k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => a_level ρ hρ k)
  rw [double_sum_eq] at hlev
  set B := ∑ j ∈ range m, aSeq ρ (j + 2) with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun j _ => (aSeq_pos ρ hρ _).le)
  have hT : ∑ i ∈ range (m + 1), Abar ρ i * ∑ j ∈ range (m + 1 - 1 - i), aSeq ρ (j + 2) ≤
      (∑ i ∈ range (m + 1), Abar ρ i) * B := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (Abar_nonneg ρ hρ i)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j _ _; exact (aSeq_pos ρ hρ _).le
  have hS := Abar_sum_le ρ hρ (m + 1)
  have hS0 : 0 ≤ ∑ i ∈ range (m + 1), Abar ρ i := Finset.sum_nonneg (fun i _ => Abar_nonneg ρ hρ i)
  have h1 : (∑ i ∈ range (m + 1), Abar ρ i) * B ≤ ρ * B := mul_le_mul_of_nonneg_right hS hBnn
  have h2 : Real.exp ρ * ∑ k ∈ range (m + 1), Abar ρ k ≤ Real.exp ρ * ρ :=
    mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
  have hfin : bSeq ρ (m + 1) - 1 ≤ ρ * B + Real.exp ρ * ρ := by
    rw [hb, hlev]; linarith
  rw [hb2] at hfin ⊢
  nlinarith

theorem Phi_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (x : ℝ) (hx : 0 ≤ x) :
    Phi ρ x * (1 - ρ) ≤ 1 := by
  have := (Phi_ge ρ hρ ⌊x⌋₊ x ⟨Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩).2
  have h2 := bSeq_bound ρ hρ hρ1 (⌊x⌋₊ + 1)
  have : Phi ρ x * (1 - ρ) ≤ bSeq ρ (⌊x⌋₊ + 1) * (1 - ρ) :=
    mul_le_mul_of_nonneg_right this (by linarith)
  linarith

/-- `π(δ, μ_S)` in terms of `Φ` -/
theorem blockProb_eq (lam δ μS : ℝ) (hlam : 0 < lam) (hμS : 0 < μS) (hδ : 0 ≤ δ) :
    blockProb lam δ μS = 1 - 1 / (1 / Phi (lam / μS) (δ * μS) + lam / μS) := by
  simp only [blockProb, bufferK, bufferP]
  rw [if_neg hμS.ne', q0_eq (lam / μS) (div_pos hlam hμS) (δ * μS) (by positivity)]

end OWSCQ


namespace OWSCQ

open OutpatientWalkIn.SmallCap Set

theorem psi_anti (ρ : ℝ) (hρ : 0 < ρ) {F G : ℝ} (hF : 1 ≤ F) (hFG : F < G) :
    1 - 1 / (1 / G + ρ) < 1 - 1 / (1 / F + ρ) := by
  have hG : 0 < G := by linarith
  have h1 : 1 / G < 1 / F := one_div_lt_one_div_of_lt (by linarith) hFG
  have h2 : 0 < 1 / G + ρ := by positivity
  have h3 : 1 / (1 / F + ρ) < 1 / (1 / G + ρ) := one_div_lt_one_div_of_lt h2 (by linarith)
  linarith

theorem C2 (lam : ℝ) (hlam : 0 < lam) (μS : ℝ) (hμS : 0 < μS) :
    StrictAntiOn (fun δ => blockProb lam δ μS) (Ici 0) ∧
      ContinuousOn (fun δ => blockProb lam δ μS) (Ici 0) := by
  set ρ := lam / μS with hρdef
  have hρ : 0 < ρ := div_pos hlam hμS
  have heq : EqOn (fun δ => blockProb lam δ μS) (fun δ => 1 - 1 / (1 / Phi ρ (δ * μS) + ρ)) (Ici 0) :=
    fun δ hδ => blockProb_eq lam δ μS hlam hμS hδ
  constructor
  · intro δ hδ δ' hδ' hlt
    rw [heq hδ, heq hδ']
    have hx : δ * μS < δ' * μS := mul_lt_mul_of_pos_right hlt hμS
    have hx0 : (0:ℝ) ≤ δ * μS := mul_nonneg hδ hμS.le
    have hx0' : (0:ℝ) ≤ δ' * μS := mul_nonneg hδ' hμS.le
    exact psi_anti ρ hρ (Phi_ge_one ρ hρ _ hx0) (Phi_strictMonoOn ρ hρ hx0 hx0' hx)
  · refine ContinuousOn.congr ?_ heq
    have hP : ContinuousOn (fun δ => Phi ρ (δ * μS)) (Ici 0) := by
      apply (Phi_continuousOn ρ hρ).comp (continuousOn_id.mul continuousOn_const)
      intro δ hδ
      exact mul_nonneg hδ hμS.le
    have hPne : ∀ δ ∈ Ici (0:ℝ), Phi ρ (δ * μS) ≠ 0 := fun δ hδ =>
      (lt_of_lt_of_le one_pos (Phi_ge_one ρ hρ _ (mul_nonneg hδ hμS.le))).ne'
    have hden : ContinuousOn (fun δ => 1 / Phi ρ (δ * μS) + ρ) (Ici 0) :=
      (continuousOn_const.div hP hPne).add continuousOn_const
    apply continuousOn_const.sub
    apply continuousOn_const.div hden
    intro δ hδ
    have := Phi_ge_one ρ hρ _ (mul_nonneg hδ hμS.le)
    have : 0 < 1 / Phi ρ (δ * μS) := by positivity
    linarith

theorem rate (lam : ℝ) (hlam : 0 < lam) (δ : ℝ) (hδ : 0 ≤ δ) (μS : ℝ) (hμS : 0 < μS) :
    lam / (1 + lam / μS) ≤ lam * (1 - blockProb lam δ μS) ∧ lam * (1 - blockProb lam δ μS) ≤ lam := by
  rw [blockProb_eq lam δ μS hlam hμS hδ]
  set ρ := lam / μS with hρdef
  have hρ : 0 < ρ := div_pos hlam hμS
  set F := Phi ρ (δ * μS) with hF
  have hx0 : (0:ℝ) ≤ δ * μS := mul_nonneg hδ hμS.le
  have hF1 : 1 ≤ F := Phi_ge_one ρ hρ _ hx0
  have hF0 : 0 < F := by linarith
  have hiF : 1 / F ≤ 1 := by rw [div_le_one hF0]; exact hF1
  have hiF0 : 0 < 1 / F := by positivity
  have hd : 0 < 1 / F + ρ := by positivity
  simp only [sub_sub_cancel]
  constructor
  · rw [mul_one_div]
    exact div_le_div_of_nonneg_left hlam.le hd (by linarith)
  · rw [mul_one_div, div_le_iff₀ hd]
    rcases le_or_gt 1 ρ with h | h
    · nlinarith
    · have := Phi_le ρ hρ h _ hx0
      rw [← hF] at this
      have : 1 - ρ ≤ 1 / F := by
        rw [le_div_iff₀ hF0]; linarith
      nlinarith

end OWSCQ

open OutpatientWalkIn.SmallCap

theorem solution (lam : ℝ) (hlam : 0 < lam) (μS : ℝ) (hμS : 0 < μS) :
    StrictAntiOn (fun δ => blockProb lam δ μS) (Set.Ici 0) ∧ ContinuousOn (fun δ => blockProb lam δ μS) (Set.Ici 0) :=
  OWSCQ.C2 lam hlam μS hμS
