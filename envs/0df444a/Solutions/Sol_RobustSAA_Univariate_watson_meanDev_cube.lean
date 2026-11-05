-- Prove2me | solution 1 for RobustSAA.Univariate.watson_meanDev_cube
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:23:41.583059+00:00
-- url     : https://prove2.me/submissions/45a11684-8bc6-4d10-a308-198db5f93abb

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

open Filter MeasureTheory RobustSAA.Univariate

namespace RSAA3W

lemma sum_lin (a h : ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, (a - k * h)) * 2 = M * (2 * a - ((M : ℝ) - 1) * h) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- Tangent-line (Jensen) lower bound for the sum of squares of an arithmetic progression. -/
lemma sum_sq_ge (a h c : ℝ) (M : ℕ) (hc : 0 ≤ c) (hcM : c ≤ 2 * a - ((M : ℝ) - 1) * h - c) :
    (M : ℝ) * c ^ 2 ≤ ∑ k ∈ Finset.range M, (a - k * h) ^ 2 := by
  have h1 : ∀ k ∈ Finset.range M, 2 * c * (a - k * h) - c ^ 2 ≤ (a - k * h) ^ 2 :=
    fun k _ => by nlinarith [sq_nonneg (a - k * h - c)]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h2
  have h3 := sum_lin a h M
  have hM : (0 : ℝ) ≤ M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcM (mul_nonneg hM hc)]

lemma u_mem {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) (i : Fin N) :
    0 ≤ u F₀ s i ∧ u F₀ s i ≤ 1 :=
  ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

lemma u_mono {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : Monotone (u F₀ s) :=
  (ProbabilityTheory.monotone_cdf _).comp (Tuple.monotone_sort s)

lemma term_le_ks {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) (i : Fin N) :
    max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N) ≤ ksStat F₀ s := by
  unfold ksStat
  exact le_ciSup (f := fun i : Fin N =>
    max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N))
    (Set.finite_range _).bddAbove i

/-- Lower bound on a sum over `Fin N` of nonnegative terms by a sum along an injective index map. -/
lemma sum_ge_of_inj {N M : ℕ} (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (φ : ℕ → ℕ)
    (hφ : ∀ k < M, φ k < N) (hinj : ∀ k1 < M, ∀ k2 < M, φ k1 = φ k2 → k1 = k2)
    (b : ℕ → ℝ) (hb : ∀ k < M, b k ≤ g (φ k)) :
    ∑ k ∈ Finset.range M, b k ≤ ∑ n ∈ Finset.range N, g n := by
  calc ∑ k ∈ Finset.range M, b k ≤ ∑ k ∈ Finset.range M, g (φ k) :=
        Finset.sum_le_sum (fun k hk => hb k (Finset.mem_range.mp hk))
    _ = ∑ n ∈ (Finset.range M).image φ, g n := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact hinj x (Finset.mem_range.mp hx) y (Finset.mem_range.mp hy) hxy
    _ ≤ ∑ n ∈ Finset.range N, g n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_range.mpr (hφ k (Finset.mem_range.mp hk))
        · intro n _ _; exact hg n



lemma sum_odd (N : ℕ) : ∑ n ∈ Finset.range N, (2 * (n : ℝ) + 1) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma alg_w (a L N : ℝ) (ha : 1 ≤ a) (hN : 2 * a ≤ N) (hL1 : a / 2 ≤ L) (hL2 : L < a / 2 + 1) :
    a ^ 3 ≤ 8 * (N / 12 + L * (a - L / 2) ^ 2) := by
  have h1 : 0 ≤ 3 * a / 4 - 1 / 2 := by linarith
  have h2 : 3 * a / 4 - 1 / 2 ≤ a - L / 2 := by linarith
  have h3 : (3 * a / 4 - 1 / 2) ^ 2 ≤ (a - L / 2) ^ 2 := pow_le_pow_left₀ h1 h2 2
  have h4 : a / 2 * (3 * a / 4 - 1 / 2) ^ 2 ≤ L * (a - L / 2) ^ 2 :=
    mul_le_mul hL1 h3 (sq_nonneg _) (by linarith)
  have h5 : 0 ≤ a * ((5 / 4) * (a - 6 / 5) ^ 2 + (7 / 3 - 9 / 5)) := by
    apply mul_nonneg (by linarith); nlinarith [sq_nonneg (a - 6 / 5)]
  nlinarith

end RSAA3W

open RSAA3W

theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    |meanDev F₀ s| ^ 3 ≤ 8 * watsonStat F₀ s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, U = fun n => if hn : n < N then u F₀ s ⟨n, hn⟩ else 1 :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * N) := ⟨_, rfl⟩
  have hUi : ∀ i : Fin N, U i = u F₀ s i := by intro i; rw [hU]; simp [i.isLt]
  have hU01 : ∀ n, 0 ≤ U n ∧ U n ≤ 1 := by
    intro n; rw [hU]; simp only
    split_ifs with hn
    · exact u_mem F₀ s _
    · norm_num
  -- sums over range N
  have hsumU : ∑ i : Fin N, u F₀ s i = ∑ n ∈ Finset.range N, U n := by
    rw [← Fin.sum_univ_eq_sum_range U N]
    exact Finset.sum_congr rfl (fun i _ => (hUi i).symm)
  have hsumQ : ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - u F₀ s i) ^ 2 =
      ∑ n ∈ Finset.range N, (U n - T n) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => (U n - T n) ^ 2) N]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hUi, hT]; ring_nf
  have hsumT : ∑ n ∈ Finset.range N, T n = N / 2 := by
    rw [hT, ← Finset.sum_div, sum_odd]; field_simp
  set m := meanDev F₀ s with hm
  have hmd : m = (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, (U n - T n) := by
    rw [hm, meanDev, hsumU, Finset.sum_sub_distrib, hsumT]; field_simp
  have hcvm : cvmStat F₀ s ^ 2 = 1 / (12 * (N : ℝ) ^ 2) +
      (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, (U n - T n) ^ 2 := by
    unfold cvmStat
    rw [Real.sq_sqrt (by positivity), hsumQ]
  -- variance identity
  have hvar : cvmStat F₀ s ^ 2 - m ^ 2 = 1 / (12 * (N : ℝ) ^ 2) +
      (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 := by
    have e1 : ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 =
        ∑ n ∈ Finset.range N, (U n - T n) ^ 2 - 2 * m * ∑ n ∈ Finset.range N, (U n - T n)
          + N * m ^ 2 := by
      have : ∀ n ∈ Finset.range N, (U n - T n - m) ^ 2 =
          (U n - T n) ^ 2 - 2 * m * (U n - T n) + m ^ 2 := fun n _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e2 : ∑ n ∈ Finset.range N, (U n - T n) = N * m := by
      rw [hmd]; field_simp
    rw [hcvm, e1, e2]
    field_simp
    ring
  have hW : cvmStat F₀ s ^ 2 - m ^ 2 ≤ watsonStat F₀ s ^ 2 := by
    unfold watsonStat
    rw [← hm]
    rcases le_total 0 (cvmStat F₀ s ^ 2 - m ^ 2) with h | h
    · rw [Real.sq_sqrt h]
    · exact le_trans h (sq_nonneg _)
  have hsq0 : 0 ≤ ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  -- |m| ≤ 1/2
  have hm2 : |m| ≤ 1 / 2 := by
    have hs0 : 0 ≤ ∑ n ∈ Finset.range N, U n := Finset.sum_nonneg (fun n _ => (hU01 n).1)
    have hs1 : ∑ n ∈ Finset.range N, U n ≤ N := by
      have := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => (hU01 n).2)
      simpa using this
    have hmu : m = (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, U n - 1 / 2 := by
      rw [hm, meanDev, hsumU]
    have h0 : 0 ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, U n := by positivity
    have h1 : (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, U n ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hNr]; exact hs1
    rw [abs_le]; constructor <;> linarith
  apply le_trans _ (mul_le_mul_of_nonneg_left hW (by norm_num))
  rw [hvar]
  set a := (N : ℝ) * |m| with ha
  have hma : |m| = a / N := by rw [ha]; field_simp
  by_cases hsmall : a ≤ 1
  · -- small: |m|^3 ≤ (1/2) (1/N)^2
    have h1 : |m| ≤ 1 / N := by rw [hma]; exact div_le_div_of_nonneg_right hsmall hNr.le
    have h2 : |m| ^ 3 ≤ (1 / 2) * (1 / (N : ℝ)) ^ 2 := by
      have hm0 : 0 ≤ |m| := abs_nonneg m
      calc |m| ^ 3 = |m| * |m| ^ 2 := by ring
        _ ≤ (1 / 2) * (1 / (N : ℝ)) ^ 2 :=
          mul_le_mul hm2 (pow_le_pow_left₀ hm0 h1 2) (sq_nonneg _) (by norm_num)
    have h3 : (1 / 2) * (1 / (N : ℝ)) ^ 2 ≤ 8 * (1 / (12 * (N : ℝ) ^ 2)) := by
      rw [div_pow, one_pow]
      have : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      rw [show 8 * (1 / (12 * (N : ℝ) ^ 2)) = (2 / 3) * (1 / (N : ℝ) ^ 2) by field_simp; ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have h4 : 0 ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 := by positivity
    linarith
  · push Not at hsmall
    have hN2a : 2 * a ≤ N := by
      rw [ha]; nlinarith [abs_nonneg m]
    obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌈a / 2⌉₊ := ⟨_, rfl⟩
    have hL1 : a / 2 ≤ L := hL ▸ Nat.le_ceil _
    have hL2 : (L : ℝ) < a / 2 + 1 := hL ▸ Nat.ceil_lt_add_one (by linarith)
    have hLN : L < N := by
      have : (L : ℝ) < N := by linarith
      exact_mod_cast this
    have hTrev : ∀ k, k < N → T (N - 1 - k) = 1 - (2 * (k : ℝ) + 1) / (2 * N) := by
      intro k hk
      rw [hT]
      dsimp only
      have : ((N - 1 - k : ℕ) : ℝ) = (N : ℝ) - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [this]; field_simp; ring
    have hkvalid : ∀ k < L, (2 * (k : ℝ) + 1) / (2 * N) ≤ |m| := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ L := by exact_mod_cast hk
      rw [hma, div_le_div_iff₀ (by positivity) hNr]
      nlinarith
    -- lower bound by an arithmetic progression
    have hlow : ∑ k ∈ Finset.range L, (|m| - (2 * (k : ℝ) + 1) / (2 * N)) ^ 2 ≤
        ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 := by
      rcases le_total 0 m with hpos | hneg
      · refine sum_ge_of_inj _ (fun n => sq_nonneg _) (fun k => N - 1 - k) ?_ ?_ _ ?_
        · intro k hk; omega
        · intro k1 hk1 k2 hk2 heq; omega
        · intro k hk
          have hv := hkvalid k hk
          have hUle := (hU01 (N - 1 - k)).2
          have hTr := hTrev k (by omega)
          rw [abs_of_nonneg hpos] at hv ⊢
          have h1 : U (N - 1 - k) - T (N - 1 - k) - m ≤ -(m - (2 * (k : ℝ) + 1) / (2 * N)) := by
            linarith
          have h2 : 0 ≤ m - (2 * (k : ℝ) + 1) / (2 * N) := by linarith
          nlinarith
      · refine sum_ge_of_inj _ (fun n => sq_nonneg _) (fun k => k) ?_ ?_ _ ?_
        · intro k hk; omega
        · intro k1 hk1 k2 hk2 heq; exact heq
        · intro k hk
          have hv := hkvalid k hk
          have hU0 := (hU01 k).1
          rw [abs_of_nonpos hneg] at hv ⊢
          have hTk : T k = (2 * (k : ℝ) + 1) / (2 * N) := by rw [hT]
          have h1 : -m - (2 * (k : ℝ) + 1) / (2 * N) ≤ U k - T k - m := by linarith
          have h2 : 0 ≤ -m - (2 * (k : ℝ) + 1) / (2 * N) := by linarith
          exact pow_le_pow_left₀ h2 h1 2
    -- Jensen
    have hc0 : 0 ≤ |m| - L / (2 * (N : ℝ)) := by
      rw [hma, div_sub_div _ _ hNr.ne' (by positivity), le_div_iff₀ (by positivity)]
      nlinarith
    have hcond : |m| - L / (2 * (N : ℝ)) ≤ 2 * (|m| - 1 / (2 * (N : ℝ))) -
        ((L : ℝ) - 1) * (1 / (N : ℝ)) - (|m| - L / (2 * (N : ℝ))) := by
      apply le_of_eq; field_simp; ring
    have hjen := sum_sq_ge (|m| - 1 / (2 * (N : ℝ))) (1 / (N : ℝ)) (|m| - L / (2 * (N : ℝ))) L
      hc0 hcond
    have hjen' : (L : ℝ) * (|m| - L / (2 * (N : ℝ))) ^ 2 ≤
        ∑ k ∈ Finset.range L, (|m| - (2 * (k : ℝ) + 1) / (2 * N)) ^ 2 := by
      refine le_trans hjen (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_)))
      congr 1; field_simp; ring
    -- final algebra
    have halg := alg_w a L N (le_of_lt hsmall) hN2a hL1 hL2
    have hkey : |m| ^ 3 ≤ 8 * (1 / (12 * (N : ℝ) ^ 2) +
        1 / (N : ℝ) * ((L : ℝ) * (|m| - L / (2 * (N : ℝ))) ^ 2)) := by
      have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
      have eL : |m| ^ 3 = a ^ 3 / (N : ℝ) ^ 3 := by rw [hma]; ring
      have eR : 8 * (1 / (12 * (N : ℝ) ^ 2) +
          1 / (N : ℝ) * ((L : ℝ) * (|m| - L / (2 * (N : ℝ))) ^ 2)) =
          8 * ((N : ℝ) / 12 + L * (a - L / 2) ^ 2) / (N : ℝ) ^ 3 := by
        rw [hma]; field_simp
      rw [eL, eR]
      exact div_le_div_of_nonneg_right halg hN3.le
    have hmono : (1 / (N : ℝ)) * ((L : ℝ) * (|m| - L / (2 * (N : ℝ))) ^ 2) ≤
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, (U n - T n - m) ^ 2 :=
      mul_le_mul_of_nonneg_left (le_trans hjen' hlow) (by positivity)
    linarith
