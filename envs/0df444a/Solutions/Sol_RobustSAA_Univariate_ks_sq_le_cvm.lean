-- Prove2me | solution 1 for RobustSAA.Univariate.ks_sq_le_cvm
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:13:58.900095+00:00
-- url     : https://prove2.me/submissions/377a7091-952d-49ff-a113-96ffc1df2f4e

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

open Filter MeasureTheory RobustSAA.Univariate

namespace RSAA3CVM

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


lemma alg1 (e a : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) (ha1 : a ≤ 1) (hc : 0 ≤ a - e / 2) :
    (a + e ^ 2 / 2) ^ 2 ≤ (a - e / 2) ^ 2 + 2 * e := by
  have h1 : (a + e ^ 2 / 2) ^ 2 - (a - e / 2) ^ 2 =
      (e * (1 + e) / 2) * (2 * a + e ^ 2 / 2 - e / 2) := by ring
  have h2 : 2 * a + e ^ 2 / 2 - e / 2 ≤ 2 := by nlinarith
  have h3 : 0 ≤ e * (1 + e) / 2 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  nlinarith

lemma alg2 (r N M c Q : ℝ) (hr : 0 < r) (hN : N = r ^ 2) (hM : r ≤ M) (hQ : M * c ^ 2 ≤ Q) :
    c ^ 2 ≤ r * ((1 / N) * Q) := by
  subst hN
  have h1 : r * c ^ 2 ≤ Q := le_trans (mul_le_mul_of_nonneg_right hM (sq_nonneg c)) hQ
  have : r * ((1 / r ^ 2) * Q) = Q / r := by field_simp
  rw [this, le_div_iff₀ hr]
  linarith

/-- The core counting bound: if the deviation `a` at index `j` is attained downwards
(`t_j - U_j = a`, `M ≤ j + 1`) or upwards (`U_j - t_j = a`, `j + M ≤ N`), then the CvM sum
dominates `∑_{k<M} (a - k/N)^2`. -/
lemma core_sum (N M j : ℕ) (hjN : j < N) (U : ℕ → ℝ)
    (hU : ∀ n m : ℕ, n ≤ m → m < N → U n ≤ U m) (a : ℝ)
    (hak : ∀ k < M, 0 ≤ a - k / (N : ℝ))
    (hcase : ((2 * (j : ℝ) + 1) / (2 * N) - U j = a ∧ M ≤ j + 1) ∨
      (U j - (2 * (j : ℝ) + 1) / (2 * N) = a ∧ j + M ≤ N)) :
    ∑ k ∈ Finset.range M, (a - k / (N : ℝ)) ^ 2 ≤
      ∑ n ∈ Finset.range N, ((2 * (n : ℝ) + 1) / (2 * N) - U n) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hjN)
  have tshift : ∀ n k : ℕ, (2 * ((n + k : ℕ) : ℝ) + 1) / (2 * N) =
      (2 * (n : ℝ) + 1) / (2 * N) + k / (N : ℝ) := by
    intro n k; push_cast; field_simp; ring
  rcases hcase with ⟨hta, hMj⟩ | ⟨hta, hMj⟩
  · refine sum_ge_of_inj _ (fun n => sq_nonneg _) (fun k => j - k) ?_ ?_ _ ?_
    · intro k hk; omega
    · intro k1 hk1 k2 hk2 heq; omega
    · intro k hk
      have hmono := hU (j - k) j (Nat.sub_le _ _) hjN
      have htt := tshift (j - k) k
      rw [show j - k + k = j by omega] at htt
      have hpos := hak k hk
      have : a - k / (N : ℝ) ≤ (2 * ((j - k : ℕ) : ℝ) + 1) / (2 * N) - U (j - k) := by linarith
      exact pow_le_pow_left₀ hpos this 2
  · refine sum_ge_of_inj _ (fun n => sq_nonneg _) (fun k => j + k) ?_ ?_ _ ?_
    · intro k hk; omega
    · intro k1 hk1 k2 hk2 heq; omega
    · intro k hk
      have hmono := hU j (j + k) (Nat.le_add_right _ _) (by omega)
      have htt := tshift j k
      have hpos := hak k hk
      have : a - k / (N : ℝ) ≤ U (j + k) - (2 * ((j + k : ℕ) : ℝ) + 1) / (2 * N) := by linarith
      have h2 := pow_le_pow_left₀ hpos this 2
      have h3 : (U (j + k) - (2 * ((j + k : ℕ) : ℝ) + 1) / (2 * N)) ^ 2 =
          ((2 * ((j + k : ℕ) : ℝ) + 1) / (2 * N) - U (j + k)) ^ 2 := by ring
      linarith

end RSAA3CVM

open RSAA3CVM

theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    ksStat F₀ s ^ 2 ≤
      max (1 / Real.sqrt N + 3 / (2 * N))
        (Real.sqrt N * cvmStat F₀ s ^ 2 + 2 / Real.sqrt N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt N := ⟨_, rfl⟩
  rw [← hr]
  have hr2 : (N : ℝ) = r ^ 2 := by rw [hr, Real.sq_sqrt hNr.le]
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hN1
  have hr0 : 0 < r := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / r := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one hr0]; exact hr1
  have her : e * r = 1 := by rw [he]; field_simp
  have hNe : 1 / (N : ℝ) = e ^ 2 := by rw [hr2, he]; ring
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin N =>
    max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N))
  have hjD : max (((j : ℕ) + 1 : ℝ) / N - u F₀ s j) (u F₀ s j - ((j : ℕ) : ℝ) / N) =
      ksStat F₀ s := hj
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ksStat F₀ s := ⟨_, rfl⟩
  rw [← hD] at hjD ⊢
  have hjN : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := by positivity
  obtain ⟨hu0, hu1⟩ := u_mem F₀ s j
  obtain ⟨tj, htj⟩ : ∃ tj : ℝ, tj = (2 * ((j : ℕ) : ℝ) + 1) / (2 * N) := ⟨_, rfl⟩
  have e1 : ((j : ℕ) + 1 : ℝ) / N = tj + e ^ 2 / 2 := by
    rw [htj, ← hNe]; field_simp; ring
  have e2 : ((j : ℕ) : ℝ) / N = tj - e ^ 2 / 2 := by
    rw [htj, ← hNe]; field_simp; ring
  rw [e1, e2] at hjD
  have htj0 : 0 ≤ tj := by rw [htj]; positivity
  have htj1 : tj + e ^ 2 / 2 ≤ 1 := by
    rw [← e1, div_le_one hNr]; exact hjN
  have htj2 : e ^ 2 / 2 ≤ tj := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) / N := by positivity
    linarith
  have hD1 : D ≤ 1 := by
    rw [← hjD]; apply max_le <;> linarith
  have hDpos : e ^ 2 / 2 ≤ D := by
    rw [← hjD]
    rcases le_total (u F₀ s j) tj with h | h
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_right _ _)
  have hD0 : 0 ≤ D := le_trans (by positivity) hDpos
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = D - e ^ 2 / 2 := ⟨_, rfl⟩
  by_cases hsmall : a < e
  · apply le_max_of_le_left
    have h3 : 3 / (2 * (N : ℝ)) = 3 * e ^ 2 / 2 := by
      rw [show 3 / (2 * (N : ℝ)) = (3 / 2) * (1 / N) by ring, hNe]; ring
    rw [h3, ← he]
    have : D ≤ e + 3 * e ^ 2 / 2 := by nlinarith
    nlinarith
  · push Not at hsmall
    apply le_max_of_le_right
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈r⌉₊ := ⟨_, rfl⟩
    have hMge : r ≤ M := hM ▸ Nat.le_ceil r
    have hMlt : (M : ℝ) < r + 1 := hM ▸ Nat.ceil_lt_add_one hr0.le
    have hMe : ((M : ℝ) - 1) * e ^ 2 < e := by
      have h1 : ((M : ℝ) - 1) < r := by linarith
      have h2 := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < e ^ 2)
      have h3 : r * e ^ 2 = e := by rw [sq, ← mul_assoc, mul_comm r e, her, one_mul]
      linarith
    have hak : ∀ k < M, 0 ≤ a - k / (N : ℝ) := by
      intro k hk
      have h1 : (k : ℝ) ≤ M - 1 := by
        have : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
        linarith
      have h2 : (k : ℝ) / N = k * e ^ 2 := by rw [div_eq_mul_one_div, hNe]
      rw [h2]
      have : (k : ℝ) * e ^ 2 ≤ ((M : ℝ) - 1) * e ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith
    obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, U = fun n => if hn : n < N then u F₀ s ⟨n, hn⟩ else 1 :=
      ⟨_, rfl⟩
    have hUj : U j = u F₀ s j := by rw [hU]; simp [j.isLt]
    have hUmono : ∀ n m : ℕ, n ≤ m → m < N → U n ≤ U m := by
      intro n m hnm hm
      have hn : n < N := lt_of_le_of_lt hnm hm
      rw [hU]
      simp only [hn, hm, dif_pos]
      exact u_mono F₀ s (show (⟨n, hn⟩ : Fin N) ≤ ⟨m, hm⟩ from hnm)
    have hcase : ((2 * ((j : ℕ) : ℝ) + 1) / (2 * N) - U j = a ∧ M ≤ (j : ℕ) + 1) ∨
        (U j - (2 * ((j : ℕ) : ℝ) + 1) / (2 * N) = a ∧ (j : ℕ) + M ≤ N) := by
      rw [hUj, ← htj]
      rcases le_total (u F₀ s j - (tj - e ^ 2 / 2)) (tj + e ^ 2 / 2 - u F₀ s j) with hc | hc
      · rw [max_eq_left hc] at hjD
        left
        refine ⟨by linarith, ?_⟩
        -- e ≤ tj gives r ≤ j + 1/2
        have h1 : e ≤ tj := by linarith
        have h2 : r ≤ ((j : ℕ) : ℝ) + 1 / 2 := by
          have h3 : tj * (2 * N) = 2 * ((j : ℕ) : ℝ) + 1 := by
            rw [htj]; field_simp
          have h4 : e * (2 * N) = 2 * r := by
            rw [hr2, he]; field_simp
          nlinarith
        have : (M : ℝ) < ((j : ℕ) : ℝ) + 2 := by linarith
        have : M < (j : ℕ) + 2 := by exact_mod_cast this
        omega
      · rw [max_eq_right hc] at hjD
        right
        refine ⟨by linarith, ?_⟩
        have h1 : tj ≤ 1 - e := by linarith
        have h2 : ((j : ℕ) : ℝ) + r ≤ N - 1 / 2 := by
          have h3 : tj * (2 * N) = 2 * ((j : ℕ) : ℝ) + 1 := by
            rw [htj]; field_simp
          have h4 : e * (2 * N) = 2 * r := by
            rw [hr2, he]; field_simp
          have h5 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * N)
          have h6 : (1 - e) * (2 * N) = 2 * N - e * (2 * N) := by ring
          linarith
        have : (((j : ℕ) + M : ℕ) : ℝ) < N + 1 := by
          push_cast
          linarith
        have : (j : ℕ) + M < N + 1 := by exact_mod_cast this
        omega
    have hmain := core_sum N M j j.isLt U hUmono a hak hcase
    have hc0 : 0 ≤ a - e / 2 := by linarith
    have hjen := sum_sq_ge a (1 / (N : ℝ)) (a - e / 2) M hc0 (by
      have : ((M : ℝ) - 1) * (1 / (N : ℝ)) < e := by rw [hNe]; exact hMe
      linarith)
    have hjen' : (M : ℝ) * (a - e / 2) ^ 2 ≤
        ∑ n ∈ Finset.range N, ((2 * (n : ℝ) + 1) / (2 * N) - U n) ^ 2 := by
      refine le_trans hjen (le_trans (le_of_eq ?_) hmain)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [div_eq_mul_one_div (k : ℝ)]
    have hQ : ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - u F₀ s i) ^ 2 =
        ∑ n ∈ Finset.range N, ((2 * (n : ℝ) + 1) / (2 * N) - U n) ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun n => ((2 * (n : ℝ) + 1) / (2 * N) - U n) ^ 2) N]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : U i = u F₀ s i := by rw [hU]; simp [i.isLt]
      rw [this]
      ring_nf
    have hcvm : cvmStat F₀ s ^ 2 = 1 / (12 * (N : ℝ) ^ 2) +
        (1 / (N : ℝ)) * ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - u F₀ s i) ^ 2 := by
      unfold cvmStat
      rw [Real.sq_sqrt]
      positivity
    have hW := alg2 r N M (a - e / 2) _ hr0 hr2 hMge hjen'
    have hfin := alg1 e a he0 he1 (by have := sq_nonneg e; linarith) hc0
    have hDa : D = a + e ^ 2 / 2 := by rw [ha]; ring
    have hext : 0 ≤ r * (1 / (12 * (N : ℝ) ^ 2)) := by positivity
    have h2r : 2 / r = 2 * e := by rw [he]; ring
    rw [hcvm, hQ, hDa, mul_add, h2r]
    linarith
