-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T12:12:29.395985+00:00
-- url     : https://prove2.me/submissions/10c0f7e6-1c02-41cb-863a-c535f5c5d723

import Definitions.Def_ZudilinZetaPartialFractions

set_option autoImplicit false


-- PartialFractionSummation

open ZudilinZeta Filter Finset
open scoped Topology

private lemma power_sequence_tendsto {s : ℕ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)^s) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hs.ne').comp h)

private lemma hasSum_shift_difference {f : ℕ → ℝ} (hf : Antitone f)
    (ht : Tendsto f atTop (𝓝 0)) (k : ℕ) :
    HasSum (fun n => f n - f (n+k)) (∑ i ∈ range k, f i) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr (hf (Nat.le_add_right n k))) _).mpr
  have htail : Tendsto (fun N : ℕ => ∑ i ∈ range k, f (N+i)) atTop (𝓝 0) := by
    simpa only [sum_const_zero, Function.comp_def] using tendsto_finsetSum (range k)
      (fun i hi => ht.comp (tendsto_add_atTop_nat i))
  have he (N : ℕ) : (∑ n ∈ range N, (f n - f (n+k))) =
      (∑ i ∈ range k, f i) - ∑ i ∈ range k, f (N+i) := by
    have h1 := sum_range_add f N k
    have h2 := sum_range_add f k N
    rw [Nat.add_comm N k] at h1
    rw [sum_sub_distrib]
    have hcomm : (∑ n ∈ range N, f (n+k)) = ∑ n ∈ range N, f (k+n) := by
      apply sum_congr rfl
      intro i hi
      rw [Nat.add_comm]
    rw [hcomm]
    linarith
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub htail

private lemma hasSum_power_difference (s k : ℕ) (hs : 0 < s) (hk : 0 < k) :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + k)^s - 1 / ((n : ℝ)+1)^s)
      (-(∑ i ∈ range (k-1), (1 : ℝ) / ((i : ℝ)+1)^s)) := by
  have hf : Antitone (fun n : ℕ => (1 : ℝ) / ((n : ℝ)+1)^s) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1) s)
  have h := (hasSum_shift_difference hf (power_sequence_tendsto hs) (k-1)).neg
  apply h.congr_fun
  intro n
  have he : ((n + (k-1) : ℕ) : ℝ) + 1 = (n : ℝ) + k := by
    rw [Nat.cast_add, Nat.cast_sub hk]
    push_cast
    ring
  rw [he]
  ring

private lemma hasSum_power_tail (s k : ℕ) (hs : 1 < s) (hk : 0 < k) :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ)+k)^s)
      (zetaR s - ∑ i ∈ range (k-1), (1 : ℝ) / ((i : ℝ)+1)^s) := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)+1)^s) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div, Function.comp_def] using
      ((Real.summable_nat_pow_inv.mpr hs).comp_injective (add_left_injective (1 : ℕ)))
  have h := (hasSum_power_difference s k hs.le hk).add hsum.hasSum
  simpa only [sub_add_cancel, neg_add_eq_sub, zetaR] using h

private lemma hasSum_partial_fraction_row (K : Finset ℕ) (c : ℕ → ℚ)
    (s : ℕ) (hs : 0 < s) (hK : ∀ k ∈ K, 0 < k)
    (hres : s = 1 → ∑ k ∈ K, c k = 0) :
    HasSum (fun n : ℕ => ∑ k ∈ K, (c k : ℝ) / ((n : ℝ)+k)^s)
      (((∑ k ∈ K, c k : ℚ) : ℝ) * zetaR s -
        ((∑ k ∈ K, c k * ∑ i ∈ range (k-1), (1 : ℚ) / ((i : ℚ)+1)^s : ℚ) : ℝ)) := by
  classical
  by_cases hs1 : s = 1
  · have hc : ∑ k ∈ K, (c k : ℝ) = 0 := by exact_mod_cast hres hs1
    have h := hasSum_sum (fun k hk => (hasSum_power_difference s k hs (hK k hk)).mul_left (c k : ℝ))
    have he (n : ℕ) : (∑ k ∈ K, (c k : ℝ) * (1 / ((n : ℝ)+k)^s - 1 / ((n : ℝ)+1)^s)) =
        ∑ k ∈ K, (c k : ℝ) / ((n : ℝ)+k)^s := by
      simp_rw [mul_sub]
      rw [sum_sub_distrib, ← sum_mul, hc, zero_mul, sub_zero]
      simp only [mul_one_div]
    simp only [he] at h
    have hv : ((∑ k ∈ K, c k : ℚ) : ℝ) * zetaR s -
        ((∑ k ∈ K, c k * ∑ i ∈ range (k-1), (1 : ℚ) / ((i : ℚ)+1)^s : ℚ) : ℝ) =
        ∑ k ∈ K, (c k : ℝ) * -(∑ i ∈ range (k-1), (1 : ℝ) / ((i : ℝ)+1)^s) := by
      push_cast
      simp only [hc, zero_mul, zero_sub, mul_neg, sum_neg_distrib]
    rw [hv]
    exact h
  · have h := hasSum_sum (fun k hk => (hasSum_power_tail s k (by omega) (hK k hk)).mul_left (c k : ℝ))
    simp only [mul_one_div] at h
    have hv : ((∑ k ∈ K, c k : ℚ) : ℝ) * zetaR s -
        ((∑ k ∈ K, c k * ∑ i ∈ range (k-1), (1 : ℚ) / ((i : ℚ)+1)^s : ℚ) : ℝ) =
        ∑ k ∈ K, (c k : ℝ) * (zetaR s - ∑ i ∈ range (k-1), (1 : ℝ) / ((i : ℝ)+1)^s) := by
      push_cast
      simp_rw [mul_sub]
      rw [sum_sub_distrib, sum_mul]
    rw [hv]
    exact h

-- PartialFractionDerivative

open ZudilinZeta Filter Finset
open scoped Topology

private lemma hasDerivAt_const_div_pow (c : ℝ) (k s : ℕ) (hs : 0 < s)
    (x : ℝ) (hx : x + k ≠ 0) :
    HasDerivAt (fun t : ℝ => c / (t+(k : ℝ))^s)
      (-(c * s) / (x+k)^(s+1)) x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have h := (hasDerivAt_const x c).div
    (((hasDerivAt_id x).add_const (k : ℝ)).fun_pow (j+1)) (pow_ne_zero _ hx)
  convert h using 1 <;> try rfl
  simp only [Nat.add_sub_cancel, pow_succ, id_eq, zero_mul, mul_one, zero_sub]
  field_simp [hx]

private lemma iteratedDeriv_const_div_pow (c : ℝ) (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (d : ℕ) {x : ℝ} (hx : -1 < x) :
    iteratedDeriv d (fun t : ℝ => c / (t+(k : ℝ))^s) x =
      (-1 : ℝ)^d * (s.ascFactorial d : ℝ) * c / (x+k)^(s+d) := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    have he : iteratedDeriv d (fun t : ℝ => c / (t+(k : ℝ))^s) =ᶠ[𝓝 x]
        fun t => (-1 : ℝ)^d * (s.ascFactorial d : ℝ) * c / (t+k)^(s+d) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hd := hasDerivAt_const_div_pow ((-1 : ℝ)^d * (s.ascFactorial d : ℝ) * c)
      k (s+d) (by omega) x (by linarith)
    rw [hd.deriv, Nat.ascFactorial_succ, pow_succ]
    push_cast
    rw [show s+(d+1) = s+d+1 by omega]
    ring

private lemma poleRange_pos (P : Params) (n k : ℕ) (hk : k ∈ poleRange P n) : 0 < k := by
  have h := (mem_Icc.mp hk).1
  have hpos : 0 < hh P n (P.r+1) := by simp [hh]
  exact hpos.trans_le h

private lemma partial_fraction_normalized_derivative (P : Params) (n : ℕ)
    (d : PartialFractionData P n) (t : ℕ) :
    (1 / ((P.r-1).factorial : ℝ)) * iteratedDeriv (P.r-1) (R P n) (t : ℝ) =
      ∑ s ∈ Icc 1 (P.q-P.r), (derivativeWeight P.r s : ℝ) *
        ∑ k ∈ poleRange P n, (d.coeff s k : ℝ) / ((t : ℝ)+k)^(s+(P.r-1)) := by
  have ht : (-1 : ℝ) < t := by have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith
  have he : R P n =ᶠ[𝓝 (t : ℝ)]
      fun x => ∑ s ∈ Icc 1 (P.q-P.r), ∑ k ∈ poleRange P n, (d.coeff s k : ℝ) / (x+k)^s := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact d.expansion x hx
  rw [he.iteratedDeriv_eq]
  have hcd (s k : ℕ) (hk : k ∈ poleRange P n) :
      ContDiffAt ℝ (P.r-1) (fun x : ℝ => (d.coeff s k : ℝ) / (x+k)^s) (t : ℝ) := by
    apply contDiffAt_const.fun_div ((contDiffAt_id.add contDiffAt_const).pow s)
    apply pow_ne_zero
    have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr (poleRange_pos P n k hk)
    positivity
  rw [iteratedDeriv_fun_sum (fun s hs => ContDiffAt.sum (fun k hk => hcd s k hk)), mul_sum]
  apply sum_congr rfl
  intro s hs
  rw [iteratedDeriv_fun_sum (fun k hk => hcd s k hk), mul_sum, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [iteratedDeriv_const_div_pow _ _ _ (poleRange_pos P n k hk) (mem_Icc.mp hs).1 _ ht]
  rw [(Nat.Odd.sub_odd P.r_odd odd_one).neg_one_pow]
  simp only [derivativeWeight, Rat.cast_div, Rat.cast_natCast, one_mul]
  ring

-- PartialFractionAlgebra
open ZudilinZeta Filter Finset
open scoped Topology

private lemma poleRange_reflection (P : Params) (n k : ℕ) (hk : k ∈ poleRange P n) :
    hh P n 0 - k ∈ poleRange P n ∧ hh P n 0 - (hh P n 0 - k) = k := by
  have hx := mem_Icc.mp hk
  have ha : 0 < hh P n (P.r+1) := by simp [hh]
  constructor
  · apply mem_Icc.mpr
    omega
  · omega

private lemma even_row_zero (P : Params) (n : ℕ) (d : PartialFractionData P n)
    (s : ℕ) (hs : s ∈ Icc 1 (P.q-P.r)) (he : Even s) :
    d.zetaCoefficient s = 0 := by
  have hsign : (-1 : ℚ)^(s+1) = -1 := (he.add_odd odd_one).neg_one_pow
  have hsum : (∑ k ∈ poleRange P n, d.coeff s k) = -(∑ k ∈ poleRange P n, d.coeff s k) := by
    rw [← sum_neg_distrib]
    apply sum_bij' (fun k hk => hh P n 0 - k) (fun k hk => hh P n 0 - k)
      (fun k hk => (poleRange_reflection P n k hk).1)
      (fun k hk => (poleRange_reflection P n k hk).1)
      (fun k hk => (poleRange_reflection P n k hk).2)
      (fun k hk => (poleRange_reflection P n k hk).2)
    intro k hk
    rw [d.reflection s hs k hk, hsign]
    ring
  have hz : ∑ k ∈ poleRange P n, d.coeff s k = 0 := by linarith
  simp only [PartialFractionData.zetaCoefficient, hz, mul_zero]

private lemma first_row_zero (P : Params) (n : ℕ) (d : PartialFractionData P n) :
    d.zetaCoefficient 1 = 0 := by
  simp only [PartialFractionData.zetaCoefficient, d.residues, mul_zero]

private lemma odd_row_reindex (P : Params) (n : ℕ) (d : PartialFractionData P n) :
    (∑ s ∈ Icc 1 (P.q-P.r), (d.zetaCoefficient s : ℝ) * zetaR (s+(P.r-1))) =
      ∑ k ∈ Icc 1 ((P.q-P.r-2)/2), (d.zetaCoefficient (2*k+1) : ℝ) * zetaR (P.r+2*k) := by
  have hr := P.r_odd.pos
  have hp := Nat.odd_iff.mp P.r_odd
  have hq := Nat.odd_iff.mp P.q_odd
  have hqr := P.q_ge
  classical
  have he : (∑ s ∈ Icc 1 (P.q-P.r), (d.zetaCoefficient s : ℝ) * zetaR (s+(P.r-1))) =
      ∑ s ∈ (Icc 1 (P.q-P.r)).filter (fun s => 1 < s ∧ Odd s),
        (d.zetaCoefficient s : ℝ) * zetaR (s+(P.r-1)) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro s hs hns
    have hnot : ¬ (1 < s ∧ Odd s) := by simpa only [mem_filter, hs, true_and] using hns
    by_cases hs1 : s = 1
    · simp only [hs1, first_row_zero P n d, Rat.cast_zero, zero_mul]
    · have hse : Even s := Nat.not_odd_iff_even.mp (fun h => hnot ⟨by have := (mem_Icc.mp hs).1; omega, h⟩)
      simp only [even_row_zero P n d s hs hse, Rat.cast_zero, zero_mul]
  rw [he]
  symm
  refine sum_bij' (fun k hk => 2*k+1) (fun s hs => (s-1)/2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    apply mem_filter.mpr
    have hk' := mem_Icc.mp hk
    refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩
    exact ⟨k, by ring⟩
  · intro s hs
    obtain ⟨hs, h1, hodd⟩ := mem_filter.mp hs
    have hs' := mem_Icc.mp hs
    have ho := Nat.odd_iff.mp hodd
    apply mem_Icc.mpr
    omega
  · intro k hk
    omega
  · intro s hs
    have ho := Nat.odd_iff.mp (mem_filter.mp hs).2.2
    omega
  · intro k hk
    congr 2
    omega

-- PartialFractionEvaluation
theorem solution (P : Params) (n : ℕ) (d : PartialFractionData P n) :
    F P n = (d.constantCoefficient : ℝ) +
      ∑ k ∈ Icc 1 ((P.q-P.r-2)/2), (d.zetaCoefficient (2*k+1) : ℝ) * zetaR (P.r+2*k) := by
  have hr := P.r_odd.pos
  have hrows (s : ℕ) (hs : s ∈ Icc 1 (P.q-P.r)) :=
    hasSum_partial_fraction_row (poleRange P n) (d.coeff s) (s+(P.r-1))
      (by have := (mem_Icc.mp hs).1; omega) (fun k hk => poleRange_pos P n k hk)
      (fun he => by
        have hs1 : s = 1 := by have := (mem_Icc.mp hs).1; omega
        simpa only [hs1] using d.residues)
  have h := hasSum_sum (fun s hs => (hrows s hs).mul_left (derivativeWeight P.r s : ℝ))
  have hval : F P n =
      ∑ s ∈ Icc 1 (P.q-P.r), (derivativeWeight P.r s : ℝ) *
        (((∑ k ∈ poleRange P n, d.coeff s k : ℚ) : ℝ) * zetaR (s+(P.r-1)) -
          ((∑ k ∈ poleRange P n, d.coeff s k *
            ∑ i ∈ range (k-1), (1 : ℚ) / ((i : ℚ)+1)^(s+(P.r-1)) : ℚ) : ℝ)) := by
    rw [F, ← tsum_mul_left]
    exact (h.congr_fun (fun t => partial_fraction_normalized_derivative P n d t)).tsum_eq
  rw [hval, ← odd_row_reindex P n d]
  simp only [PartialFractionData.constantCoefficient, PartialFractionData.zetaCoefficient]
  push_cast
  simp_rw [mul_sub, ← mul_assoc]
  rw [sum_sub_distrib]
  ring
