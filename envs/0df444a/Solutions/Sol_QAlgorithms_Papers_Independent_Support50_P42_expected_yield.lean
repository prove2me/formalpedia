-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.expected_yield
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:45:25.853483+00:00
-- url     : https://prove2.me/submissions/2ea82baa-03d0-41d3-931a-a8d5b2564c0d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== P42EY =====

noncomputable section

open scoped BigOperators
open Filter Topology
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50.P42

namespace X4P42Y

lemma w_eval (n k : ℕ) (p : ℝ) :
    (bernsteinPolynomial ℝ n k).eval p = schmidtOutcomeWeight n p k := by
  simp [bernsteinPolynomial, schmidtOutcomeWeight]; ring

lemma sum_w (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n+1), schmidtOutcomeWeight n p k = 1 := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ n)
  simpa [Polynomial.eval_finsetSum, w_eval] using this

lemma sum_kw (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n+1), (k : ℝ) * schmidtOutcomeWeight n p k = n * p := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul ℝ n)
  simpa [Polynomial.eval_finsetSum, w_eval, nsmul_eq_mul] using this

lemma w_nonneg (n k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ schmidtOutcomeWeight n p k := by
  unfold schmidtOutcomeWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma w_le_one (n k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hk : k ≤ n) :
    schmidtOutcomeWeight n p k ≤ 1 := by
  rw [← sum_w n p]
  exact Finset.single_le_sum (f := fun j => schmidtOutcomeWeight n p j)
    (fun j _ => w_nonneg n j hp hp1) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- termwise identity in natural logs -/
lemma term (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    schmidtOutcomeWeight n p k * (Real.log (n.choose k) - Real.log (schmidtOutcomeWeight n p k)) =
      -(schmidtOutcomeWeight n p k * ((k : ℝ) * Real.log p + ((n : ℝ) - k) * Real.log (1 - p))) := by
  by_cases hw : schmidtOutcomeWeight n p k = 0
  · rw [hw]; ring
  · have hC : (n.choose k : ℝ) ≠ 0 := by
      intro h; apply hw; simp [schmidtOutcomeWeight, h]
    have h1 : (1 - p) ^ (n - k) ≠ 0 := by
      intro h; apply hw; simp [schmidtOutcomeWeight, h]
    have h2 : p ^ k ≠ 0 := by
      intro h; apply hw; simp [schmidtOutcomeWeight, h]
    have : Real.log (schmidtOutcomeWeight n p k) =
        Real.log (n.choose k) + (((n - k : ℕ) : ℝ) * Real.log (1 - p)) + (k : ℝ) * Real.log p := by
      unfold schmidtOutcomeWeight
      rw [Real.log_mul (mul_ne_zero hC h1) h2, Real.log_mul hC h1, Real.log_pow, Real.log_pow]
    rw [this, Nat.cast_sub hk]; ring

lemma ident (n : ℕ) (p : ℝ) :
    projectedYield n p + outcomeEntropy (fun k : Fin (n+1) => schmidtOutcomeWeight n p k.val) =
      (n : ℝ) * binEntropy2 p := by
  unfold projectedYield outcomeEntropy binEntropy2
  rw [Fin.sum_univ_eq_sum_range (fun k => schmidtOutcomeWeight n p k * Real.logb 2 (schmidtOutcomeWeight n p k))]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  have hl : Real.log 2 ≠ 0 := by positivity
  have : ∀ k ∈ Finset.range (n+1), schmidtOutcomeWeight n p k * Real.logb 2 (n.choose k : ℝ) -
      schmidtOutcomeWeight n p k * Real.logb 2 (schmidtOutcomeWeight n p k) =
      -(schmidtOutcomeWeight n p k * ((k : ℝ) * Real.log p + ((n : ℝ) - k) * Real.log (1 - p))) /
        Real.log 2 := by
    intro k hk
    rw [← term n k p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    unfold Real.logb; field_simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  rw [Real.binEntropy]
  simp only [Real.log_inv]
  have e1 := sum_kw n p
  have e2 := sum_w n p
  rw [Finset.sum_congr rfl (fun k _ => show -(schmidtOutcomeWeight n p k *
      ((k : ℝ) * Real.log p + ((n : ℝ) - k) * Real.log (1 - p))) =
      -Real.log p * ((k : ℝ) * schmidtOutcomeWeight n p k) +
        -Real.log (1 - p) * ((n : ℝ) * schmidtOutcomeWeight n p k) +
        Real.log (1 - p) * ((k : ℝ) * schmidtOutcomeWeight n p k) by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, e1, e2]
  field_simp
  ring

lemma entropy_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ outcomeEntropy (fun k : Fin (n+1) => schmidtOutcomeWeight n p k.val) := by
  unfold outcomeEntropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun k _ => ?_
  have h0 := w_nonneg n k.val hp hp1
  have h1 := w_le_one n k.val hp hp1 (Nat.lt_succ_iff.1 k.2)
  exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos (by norm_num) h0 h1)

lemma entropy_le (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    outcomeEntropy (fun k : Fin (n+1) => schmidtOutcomeWeight n p k.val) ≤ Real.logb 2 (n+1 : ℕ) := by
  unfold outcomeEntropy
  set N : ℝ := ((n+1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  have hl : 0 < Real.log 2 := by positivity
  -- termwise Gibbs: -w log w - w log N ≤ 1/N - w
  have key : ∀ k : Fin (n+1), -(schmidtOutcomeWeight n p k.val * Real.log (schmidtOutcomeWeight n p k.val))
      - schmidtOutcomeWeight n p k.val * Real.log N ≤ 1 / N - schmidtOutcomeWeight n p k.val := by
    intro k
    set w := schmidtOutcomeWeight n p k.val
    have h0 : 0 ≤ w := w_nonneg n k.val hp hp1
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have := Real.log_le_sub_one_of_pos (show 0 < 1 / (N * w) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul hN.ne' h.ne'] at this
      have := mul_le_mul_of_nonneg_left this h.le
      have e : w * ((N * w)⁻¹ - 1) = 1 / N - w := by field_simp
      nlinarith [this, e]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => key k)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.sum_mul,
    Fin.sum_univ_eq_sum_range (fun k => schmidtOutcomeWeight n p k), sum_w] at hsum
  have hNn : (n + 1) • (1 / N) = 1 := by
    rw [nsmul_eq_mul]; simp only [N]; push_cast; field_simp
  rw [hNn] at hsum
  simp only [one_mul, sub_self] at hsum
  show -∑ k : Fin (n+1), schmidtOutcomeWeight n p k.val * Real.logb 2 (schmidtOutcomeWeight n p k.val)
    ≤ Real.logb 2 N
  -- convert to logb
  have : -∑ k : Fin (n+1), schmidtOutcomeWeight n p k.val * Real.logb 2 (schmidtOutcomeWeight n p k.val) =
      (∑ k : Fin (n+1), -(schmidtOutcomeWeight n p k.val * Real.log (schmidtOutcomeWeight n p k.val))) /
        Real.log 2 := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold Real.logb; ring
  rw [this, Real.logb, div_le_div_iff_of_pos_right hl]
  have : ∑ k : Fin (n+1), -(schmidtOutcomeWeight n p k.val * Real.log (schmidtOutcomeWeight n p k.val)) =
      -∑ k : Fin (n+1), schmidtOutcomeWeight n p k.val * Real.log (schmidtOutcomeWeight n p k.val) := by
    rw [Finset.sum_neg_distrib]
  rw [this]; linarith

lemma bounds (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (n : ℝ)*binEntropy2 p-Real.logb 2 (n+1 : ℕ)≤projectedYield n p ∧
      projectedYield n p≤(n : ℝ)*binEntropy2 p := by
  have h := ident n p
  have h1 := entropy_nonneg n hp hp1
  have h2 := entropy_le n hp hp1
  constructor <;> linarith

lemma limit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => projectedYield (n+1) p/(((n+1 : ℕ) : ℝ)*binEntropy2 p)) atTop (𝓝 1) := by
  have hh : 0 < binEntropy2 p := div_pos (Real.binEntropy_pos hp hp1) (by positivity)
  set c := Real.log 2 * binEntropy2 p
  have hc : 0 < c := by positivity
  -- lower bound sequence → 1
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) / (c * ((n : ℝ) + 2) + -c)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop c (-c) 1 hc.ne').comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using this
  have hlow : Tendsto (fun n : ℕ => 1 - Real.logb 2 ((n+1+1 : ℕ) : ℝ) / (((n+1 : ℕ) : ℝ) * binEntropy2 p))
      atTop (𝓝 1) := by
    have : (fun n : ℕ => 1 - Real.logb 2 ((n+1+1 : ℕ) : ℝ) / (((n+1 : ℕ) : ℝ) * binEntropy2 p)) =
        fun n : ℕ => 1 - Real.log ((n : ℝ) + 2) / (c * ((n : ℝ) + 2) + -c) := by
      funext n
      congr 1
      unfold Real.logb
      push_cast
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring, div_div]
      congr 1; simp only [c]; ring
    rw [this]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · have hb := (bounds (n+1) hp.le hp1.le).1
    have hd : 0 < ((n+1 : ℕ) : ℝ) * binEntropy2 p := by positivity
    rw [le_div_iff₀ hd, sub_mul, one_mul, div_mul_cancel₀ _ hd.ne']
    exact hb
  · have hb := (bounds (n+1) hp.le hp1.le).2
    have hd : 0 < ((n+1 : ℕ) : ℝ) * binEntropy2 p := by positivity
    rw [div_le_one hd]; exact hb

lemma ends (n : ℕ) : projectedYield n 0=0 ∧ projectedYield n 1=0 := by
  constructor
  · unfold projectedYield
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · simp [schmidtOutcomeWeight, zero_pow h.ne']
  · unfold projectedYield
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases hk.eq_or_lt with h | h
    · subst h; simp
    · simp [schmidtOutcomeWeight, zero_pow (Nat.sub_pos_of_lt h).ne']

end X4P42Y

theorem solution (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (∀ n : ℕ, projectedYield n p+
      outcomeEntropy (fun k : Fin (n+1) => schmidtOutcomeWeight n p k.val)=(n : ℝ)*binEntropy2 p) ∧
    (∀ n : ℕ, (n : ℝ)*binEntropy2 p-Real.logb 2 (n+1 : ℕ)≤projectedYield n p ∧
      projectedYield n p≤(n : ℝ)*binEntropy2 p) ∧
    (0<p → p<1 → Filter.Tendsto
      (fun n : ℕ => projectedYield (n+1) p/(((n+1 : ℕ) : ℝ)*binEntropy2 p))
        Filter.atTop (nhds (1 : ℝ))) ∧
    (∀ n : ℕ, projectedYield n 0=0 ∧ projectedYield n 1=0) :=
  ⟨fun n => X4P42Y.ident n p, fun n => X4P42Y.bounds n hp hp1, fun h0 h1 => X4P42Y.limit h0 h1,
    X4P42Y.ends⟩

#print axioms solution
