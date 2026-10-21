-- Prove2me | solution 1 for SteutelVanHarn.SelfDec.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:06:40.229334+00:00
-- url     : https://prove2.me/submissions/e1eb164c-6b74-4668-8d85-c2b228fbcddc

import Mathlib
import Definitions.Def_SteutelVanHarn_SelfDec_PGF

set_option autoImplicit false
open Filter Topology

namespace SVSAux
open SteutelVanHarn.SelfDec

theorem deriv_pgf (p : ℕ → ℝ) (hp : IsDistribution p) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (pgf p) (∑' n : ℕ, p n * ((n : ℝ) * x ^ (n - 1))) x ∧
      Summable (fun n : ℕ => p n * ((n : ℝ) * x ^ (n - 1))) := by
  have hnn := hp.1
  have hp1 : ∀ n, p n ≤ 1 := fun n => by
    have := le_hasSum hp.2 n (fun m _ => hnn m)
    exact this
  set ρ : ℝ := (1 + x) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hxρ : x < ρ := by rw [hρ]; linarith
  have hu : Summable (fun n : ℕ => ρ⁻¹ * ((n : ℝ) * ρ ^ n)) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ) (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
    simpa using this.mul_left ρ⁻¹
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-ρ) ρ →
      ‖p n * ((n : ℝ) * y ^ (n - 1))‖ ≤ ρ⁻¹ * ((n : ℝ) * ρ ^ n) := by
    intro n y hy
    have hy' : |y| ≤ ρ := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hnn _), abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
      have h1 : |y| ^ m ≤ ρ ^ m := pow_le_pow_left₀ (abs_nonneg _) hy' m
      have h2 : ρ⁻¹ * (((m : ℝ) + 1) * ρ ^ (m + 1)) = ((m : ℝ) + 1) * ρ ^ m := by
        rw [pow_succ]; field_simp
      rw [h2]
      have h3 : 0 ≤ (m : ℝ) + 1 := by positivity
      calc p (m + 1) * (((m : ℝ) + 1) * |y| ^ m) ≤ 1 * (((m : ℝ) + 1) * |y| ^ m) :=
            mul_le_mul_of_nonneg_right (hp1 _) (by positivity)
        _ ≤ 1 * (((m : ℝ) + 1) * ρ ^ m) := by gcongr
        _ = _ := one_mul _
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-ρ) ρ →
      HasDerivAt (fun z : ℝ => p n * z ^ n) (p n * ((n : ℝ) * y ^ (n - 1))) y :=
    fun n y _ => (hasDerivAt_pow n y).const_mul (p n)
  have hsum0 : Summable (fun n : ℕ => p n * x ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hnn n) (pow_nonneg hx0.le n))
      (fun n => ?_) hp.2.summable
    calc p n * x ^ n ≤ p n * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hx0.le hx1.le) (hnn n)
      _ = p n := mul_one _
  have hxt : x ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hxρ⟩
  refine ⟨?_, ?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hbound hxt hsum0 hxt
  · exact Summable.of_norm_bounded hu (fun n => hbound n x hxt)

theorem key_ineq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    (n : ℝ) * (1 - x) * x ^ (n - 1) ≤ 1 := by
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hs : ((m : ℝ) + 1) * x ^ m ≤ ∑ k ∈ Finset.range (m + 1), x ^ k := by
      have := Finset.card_nsmul_le_sum (Finset.range (m + 1)) (fun k => x ^ k) (x ^ m)
        (fun k hk => pow_le_pow_of_le_one h0 h1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
      simpa using this
    have hg := geom_sum_mul_neg x (m + 1)
    have h2 : 0 ≤ 1 - x := by linarith
    have := mul_le_mul_of_nonneg_right hs h2
    have h3 : 0 ≤ x ^ (m + 1) := pow_nonneg h0 _
    nlinarith

end SVSAux

open SteutelVanHarn.SelfDec in
theorem solution (p : ℕ → ℝ) (hp : IsDistribution p) :
    Tendsto (fun x : ℝ => (1 - x) * deriv (pgf p) x) (𝓝[<] 1) (𝓝 0) := by
  have hnn := hp.1
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- choose N with small tail
  have hT := hp.2.tendsto_sum_nat
  obtain ⟨N, hN⟩ := (hT.eventually (lt_mem_nhds (by linarith : 1 - ε / 2 < 1))).exists
  set S : ℝ := ∑ i ∈ Finset.range N, p i with hS
  set C : ℝ := ∑ i ∈ Finset.range N, (i : ℝ) * p i with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hnn i))
  refine ⟨min 1 (ε / (2 * (C + 1))), lt_min one_pos (by positivity), ?_⟩
  intro x hx hdist
  have hx1 : x < 1 := hx
  rw [Real.dist_eq] at hdist
  have hδ1 : |x - 1| < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hδ2 : |x - 1| < ε / (2 * (C + 1)) := lt_of_lt_of_le hdist (min_le_right _ _)
  rw [abs_of_neg (by linarith)] at hδ1 hδ2
  have hx0 : 0 < x := by linarith
  obtain ⟨hd, hsum⟩ := SVSAux.deriv_pgf p hp hx0 hx1
  rw [hd.deriv, Real.dist_eq, sub_zero]
  set a : ℕ → ℝ := fun n => p n * ((n : ℝ) * x ^ (n - 1)) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (hnn n) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0.le _))
  have h1x : 0 < 1 - x := by linarith
  let b : ℕ → ℝ := fun n => (if n < N then (1 - x) * ((n : ℝ) * p n) else 0) + (p n - if n < N then p n else 0)
  have hf : HasSum (fun n : ℕ => if n < N then (1 - x) * ((n : ℝ) * p n) else 0) ((1 - x) * C) := by
    have : HasSum (fun n : ℕ => if n < N then (1 - x) * ((n : ℝ) * p n) else 0)
        (∑ n ∈ Finset.range N, (fun n : ℕ => if n < N then (1 - x) * ((n : ℝ) * p n) else 0) n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp at hn; simp [not_lt.2 hn])
    convert this using 1
    rw [hC, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n hn => by simp at hn; simp [hn])
  have hg : HasSum (fun n : ℕ => p n - if n < N then p n else 0) (1 - S) := by
    have : HasSum (fun n : ℕ => if n < N then p n else 0)
        (∑ n ∈ Finset.range N, (fun n : ℕ => if n < N then p n else 0) n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp at hn; simp [not_lt.2 hn])
    have e : ∑ n ∈ Finset.range N, (if n < N then p n else 0) = S := by
      rw [hS]; exact Finset.sum_congr rfl (fun n hn => by simp at hn; simp [hn])
    rw [e] at this
    exact hp.2.sub this
  have hb : HasSum b ((1 - x) * C + (1 - S)) := hf.add hg
  have hle : ∀ n, (1 - x) * a n ≤ b n := by
    intro n
    by_cases hn : n < N
    · simp only [b, hn, if_true, sub_self, add_zero]
      simp only [ha]
      have hxn : x ^ (n - 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
      have : 0 ≤ p n * (n : ℝ) := mul_nonneg (hnn n) (Nat.cast_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left hxn this]
    · simp only [b, hn, if_false, zero_add, sub_zero]
      simp only [ha]
      have hk := SVSAux.key_ineq x hx0.le hx1.le n
      have := mul_le_mul_of_nonneg_left hk (hnn n)
      nlinarith
  have hsum2 := (hsum.mul_left (1 - x)).tsum_le_tsum hle hb.summable
  rw [tsum_mul_left, hb.tsum_eq] at hsum2
  have hnonneg : 0 ≤ (1 - x) * ∑' n, a n := mul_nonneg h1x.le (tsum_nonneg ha0)
  rw [abs_of_nonneg hnonneg]
  have hc : (1 - x) * C < ε / 2 := by
    have h5 : (1 - x) * C ≤ ε / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right (by linarith) hC0
    have h6 : ε / (2 * (C + 1)) * C < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  linarith
