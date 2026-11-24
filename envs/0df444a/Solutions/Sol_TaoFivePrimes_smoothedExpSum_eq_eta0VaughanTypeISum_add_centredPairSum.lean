-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T10:12:10.755215+00:00
-- url     : https://prove2.me/submissions/97ecb023-d91f-45fc-9215-95565d95dd3b

import Theorems.Thm_TaoFivePrimes_vaughan_identity_interface
open ArithmeticFunction Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius BigOperators
namespace TaoFivePrimes
@[simp] theorem arithmeticRestrictGT_apply (B n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictGT B f n = if B < n then f n else 0 := rfl
@[simp] theorem arithmeticRestrictLE_apply (B n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictLE B f n = if n ≤ B then f n else 0 := rfl
theorem eta0_eq_zero_of_le_one_fourth {t : ℝ} (h : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log (2 * t) ≤ Real.log 2 + Real.log (1 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : Real.log (1 / 4) = -(2 * Real.log 2) := by
      rw [show (1 : ℝ) / 4 = (2 : ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      ring
    have h3 : Real.log (2 * t) ≤ -Real.log 2 := by rw [h2] at h1; linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := by
      have : Real.log 2 ≤ -Real.log (2 * t) := by linarith
      calc Real.log 2 ≤ -Real.log (2 * t) := this
        _ ≤ |Real.log (2 * t)| := neg_le_abs _
    rw [max_eq_left (by linarith)]
    ring
  · rfl
theorem eta0_eq_zero_of_one_le {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log 2 ≤ Real.log (2 * t) := by
      apply Real.log_le_log (by norm_num); linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := le_trans h1 (le_abs_self _)
    rw [max_eq_left (by linarith)]
    ring
  · rfl
theorem eta0_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : eta0 t = 0 := by
  unfold eta0
  rw [if_neg (by linarith)]
private theorem eta0VaughanTest_eq_zero_of_small {x alpha : ℝ} (hx : 0 < x) {n : ℕ}
    (h : 4 * (n : ℝ) ≤ x) : eta0VaughanTest x alpha n = 0 := by
  have h1 : (n : ℝ) / x ≤ 1 / 4 := by
    rw [div_le_iff₀ hx]; linarith
  by_cases hc : n.Coprime 2
  · rw [eta0VaughanTest, if_pos hc, eta0_eq_zero_of_le_one_fourth h1]
    simp
  · rw [eta0VaughanTest, if_neg hc]
private theorem eta0VaughanTest_eq_zero_of_big {x alpha : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : ⌊x⌋₊ + 1 ≤ n) : eta0VaughanTest x alpha n = 0 := by
  have hnR : x < (n : ℝ) := by
    have h1 : ((⌊x⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have h3 : (1 : ℝ) ≤ (n : ℝ) / x := by
    rw [le_div_iff₀ hx]; linarith
  by_cases h : n.Coprime 2
  · rw [eta0VaughanTest, if_pos h, eta0_eq_zero_of_one_le h3]
    simp
  · rw [eta0VaughanTest, if_neg h]
private theorem smoothedExpSum_eq_sum (x alpha : ℝ) (hx : 0 < x) (N : ℕ) (hN : x < N) :
    smoothedExpSum eta0 2 x alpha
      = ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          eta0VaughanTest x alpha n := by
  unfold smoothedExpSum
  have hz : ∀ n : ℕ, n ∉ Finset.range N →
      (if Nat.Coprime n 2 then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        expCircle (alpha * n) * ((eta0 ((n : ℝ) / x) : ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) / x := by
      rw [le_div_iff₀ hx]
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [eta0_eq_zero_of_one_le h1]
    simp
  rw [tsum_eq_sum hz]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold eta0VaughanTest
  split_ifs with h
  · push_cast; ring
  · ring
private theorem sum_dirichlet_pairing' (a b : ArithmeticFunction ℝ) (F : ℕ → ℂ) (N : ℕ)
    (hF : ∀ n, N ≤ n → F n = 0) :
    ∑ n ∈ Finset.range N, (((a * b) n : ℝ) : ℂ) * F n
      = ∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ((a d : ℝ) : ℂ) * ((b m : ℝ) : ℂ) * F (d * m) := by
  classical
  set g : ℕ × ℕ → ℂ := fun p => ((a p.1 : ℝ) : ℂ) * ((b p.2 : ℝ) : ℂ) * F (p.1 * p.2) with hg
  have hRHS : ∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ((a d : ℝ) : ℂ) * ((b m : ℝ) : ℂ) * F (d * m)
      = ∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), g p := by
    rw [Finset.sum_product]
  have hLHS : ∑ n ∈ Finset.range N, (((a * b) n : ℝ) : ℂ) * F n
      = ∑ p ∈ (Finset.range N).biUnion (fun n => n.divisorsAntidiagonal), g p := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpn : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [hg]; simp only; rw [hpn]
    · intro i _ j _ hij
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hpi hpj
      have h1 := (Nat.mem_divisorsAntidiagonal.mp hpi).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp hpj).1
      exact hij (h1 ▸ h2 ▸ rfl)
  rw [hLHS, hRHS]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_range] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    have hmem := Nat.mem_divisorsAntidiagonal.mp hpn
    have h1 : p.1 ≤ n := by
      rw [← hmem.1]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by
        rintro h; rw [h, mul_zero] at hmem; exact hmem.2 hmem.1.symm))
    have h2 : p.2 ≤ n := by
      rw [← hmem.1]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by
        rintro h; rw [h, zero_mul] at hmem; exact hmem.2 hmem.1.symm))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt h1 hn),
      Finset.mem_range.mpr (lt_of_le_of_lt h2 hn)⟩
  · intro p hp hpn
    simp only [Finset.mem_biUnion, Finset.mem_range, not_exists] at hpn
    rw [hg]; simp only
    rcases Nat.eq_zero_or_pos p.1 with h1 | h1
    · rw [h1]; simp
    rcases Nat.eq_zero_or_pos p.2 with h2 | h2
    · rw [h2]; simp
    have hz : N ≤ p.1 * p.2 := by
      by_contra hc
      push_neg at hc
      exact (hpn (p.1 * p.2)) ⟨hc, Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩⟩
    rw [hF _ hz]; ring
theorem eta0VaughanTest_eq_zero_of_le_V (x alpha U V : ℝ) (hx : 0 < x) (hU : 1 ≤ U)
    (hV : 0 ≤ V) (hUV : U * V ≤ x / 4) {n : ℕ} (hn : (n : ℝ) ≤ V) :
    eta0VaughanTest x alpha n = 0 := by
  apply eta0VaughanTest_eq_zero_of_small hx
  have hVU : V ≤ U * V := by
    nlinarith [mul_nonneg hV (by linarith : (0 : ℝ) ≤ U - 1)]
  have h4 : 4 * V ≤ x := by nlinarith [hUV, hVU]
  nlinarith

private theorem truncated_vonMangoldt_divisor_sum_eq_zero_of_le
    (V w : ℕ) (hw : w ≤ V) :
    (arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, hwne⟩
  have hdle : d ≤ V := (Nat.le_of_dvd (Nat.pos_of_ne_zero hwne) hdvd).trans hw
  simp [arithmeticRestrictGT, Nat.not_lt.mpr hdle]
private theorem gt_mul_zeta_sub_truncHalfLog (V : ℝ) (hV : 0 ≤ V) (w : ℕ) :
    (arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w -
      (if ⌊V⌋₊ < w then (1 / 2 : ℝ) * Real.log w else 0) =
    if V < w then theorem51Centered V w else 0 := by
  by_cases hVw : V < w
  · rw [if_pos hVw, if_pos ((Nat.floor_lt hV).2 hVw)]
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    unfold theorem51Centered
    rw [Finset.sum_filter]
    simp only [arithmeticRestrictGT_apply, Nat.floor_lt hV]
    ring
  · rw [if_neg hVw]
    have hwV : w ≤ V := le_of_not_gt hVw
    have hle : w ≤ ⌊V⌋₊ := (Nat.le_floor_iff hV).2 hwV
    rw [truncated_vonMangoldt_divisor_sum_eq_zero_of_le _ _ hle, if_neg (Nat.not_lt.mpr hle)]
    ring
private theorem eta0VaughanTest_apply (x alpha : ℝ) (n : ℕ) :
    eta0VaughanTest x alpha n =
      (if n.Coprime 2 then expCircle (alpha * n) * ((eta0 ((n : ℝ) / x) : ℝ) : ℂ) else 0) := rfl
private theorem eta0VaughanTest_zero (x alpha : ℝ) : eta0VaughanTest x alpha 0 = 0 := by
  simp [eta0VaughanTest]
private theorem eta0VaughanTest_eq_zero_of_coprime_eta0 {x alpha : ℝ} {n : ℕ}
    (hc : n.Coprime 2) (hz : eta0 ((n : ℝ) / x) = 0) : eta0VaughanTest x alpha n = 0 := by
  rw [eta0VaughanTest, if_pos hc]
  simp [hz]
private theorem eta0VaughanTest_support {x alpha : ℝ} (hx : 0 < x) {d w : ℕ}
    (h : eta0VaughanTest x alpha (d * w) ≠ 0) :
    d < ⌊x⌋₊ + 1 ∧ w < ⌊x⌋₊ + 1 := by
  have hcop : (d * w).Coprime 2 := by
    by_contra hc
    exact h (by rw [eta0VaughanTest_apply]; simp [hc])
  have heta : eta0 (((d * w : ℕ) : ℝ) / x) ≠ 0 := by
    intro hz
    exact h (eta0VaughanTest_eq_zero_of_coprime_eta0 hcop hz)
  have ht1 : ((d * w : ℕ) : ℝ) / x < 1 := by
    by_contra hge
    push_neg at hge
    exact heta (eta0_eq_zero_of_one_le hge)
  have ht0 : 0 < ((d * w : ℕ) : ℝ) / x := by
    by_contra hle
    push_neg at hle
    exact h (eta0VaughanTest_eq_zero_of_coprime_eta0 hcop (eta0_eq_zero_of_nonpos hle))
  have hdw : d * w < ⌊x⌋₊ + 1 := by
    have hlt : ((d * w : ℕ) : ℝ) < x := (div_lt_one hx).mp ht1
    have h1 : d * w ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx.le).2 hlt.le
    omega
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd (eta0VaughanTest_zero x alpha) h
    · exact h0
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0, mul_zero] at h
      exact absurd (eta0VaughanTest_zero x alpha) h
    · exact h0
  constructor
  · exact lt_of_le_of_lt (Nat.le_mul_of_pos_right d hw0) hdw
  · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left w hd0) hdw
end TaoFivePrimes
open TaoFivePrimes
theorem solution (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) *
            ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
        else 0) := by
  classical
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hV0 : (0 : ℝ) ≤ V := by linarith
  have hx : (0 : ℝ) < x := by linarith
  have hN : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_floor_add_one x
  rw [smoothedExpSum_eq_sum x alpha hx (⌊x⌋₊ + 1) hN]
  have hid := TaoFivePrimes.vaughan_identity_interface ⌊U⌋₊ ⌊V⌋₊
  have hstep : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
            - TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
              TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
            + TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
              TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
            + TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) hid
    rw [← hn]
  rw [hstep]
  have hsplit4 : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
          - TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          + TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          + TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) *
          TaoFivePrimes.eta0VaughanTest x alpha n)
      = (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha n)
        - (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha n)
        + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha n)
        + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha n) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg]
    push_cast
    ring
  rw [hsplit4]
  have hDzero : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha n) = 0 := by
    refine Finset.sum_eq_zero (fun n _ => ?_)
    by_cases hLL : TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt n = 0
    · rw [hLL]; simp
    · have hn : (n : ℝ) ≤ V := by
        have hle : n ≤ ⌊V⌋₊ := by
          by_contra hlt
          rw [arithmeticRestrictLE_apply, if_neg hlt] at hLL
          exact hLL rfl
        exact (by exact_mod_cast hle : (n : ℝ) ≤ (⌊V⌋₊ : ℝ)).trans (Nat.floor_le hV0)
      rw [eta0VaughanTest_eq_zero_of_le_V x alpha U V hx (by linarith) hV0 hUVx hn]; simp
  rw [hDzero, add_zero]
  have hA := sum_dirichlet_pairing'
    (TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
    ArithmeticFunction.log (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1)
    (fun n hn => eta0VaughanTest_eq_zero_of_big hx hn)
  have hB := sum_dirichlet_pairing'
    (TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
      TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1)
    (fun n hn => eta0VaughanTest_eq_zero_of_big hx hn)
  have hCD := sum_dirichlet_pairing'
    (TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
    (TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
    (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1)
    (fun n hn => eta0VaughanTest_eq_zero_of_big hx hn)
  rw [hA, hB]
  have hassoc : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
        TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha n)
      = (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
        (TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) n : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha n) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_assoc]
  rw [hassoc, hCD]
  have hzs : (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
        (((TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
      = (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
        ((TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
        + (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
        (((if V < (w : ℝ) then TaoFivePrimes.theorem51Centered V w else 0 : ℝ)) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha (d * w))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have h2 : (TaoFivePrimes.arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w
        = TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w +
          (if V < (w : ℝ) then TaoFivePrimes.theorem51Centered V w else 0) := by
      have h3 : TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w
          = if ⌊V⌋₊ < w then (1 / 2 : ℝ) * Real.log w else 0 := rfl
      have h4 := gt_mul_zeta_sub_truncHalfLog V hV0 w
      rw [h3]
      linarith
    rw [h2]
    push_cast
    ring
  rw [hzs]
  rw [← add_assoc, ← TaoFivePrimes.typeIExpansion_three_bilinear_sums x alpha U V hx]
  congr 1
  have hsupp : ∀ d w : ℕ,
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
        ((if V < (w : ℝ) then TaoFivePrimes.theorem51Centered V w else 0 : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha (d * w)) ≠ 0 →
      d ∈ Finset.range (⌊x⌋₊ + 1) ∧ w ∈ Finset.range (⌊x⌋₊ + 1) := by
    intro d w hne
    have hT : TaoFivePrimes.eta0VaughanTest x alpha (d * w) ≠ 0 := by
      intro hz; exact hne (by rw [hz]; ring)
    obtain ⟨hd, hw⟩ := eta0VaughanTest_support hx hT
    exact ⟨Finset.mem_range.mpr hd, Finset.mem_range.mpr hw⟩
  have hCc : (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      (((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
        ((if V < (w : ℝ) then TaoFivePrimes.theorem51Centered V w else 0 : ℝ) : ℂ) *
        TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
      = (∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) *
            ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
        else 0)) := by
    rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1)) (fun d hd => by
      have hz : ∀ w : ℕ, (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
              TaoFivePrimes.expCircle (alpha * d * w) *
              ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) = 0 := by
        intro w
        by_contra hne
        have hc : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 := by
          by_contra hc2; exact hne (if_neg hc2)
        have heta : TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) ≠ 0 := by
          intro hz2; exact hne (by rw [if_pos hc, hz2]; simp)
        have hdw : (d : ℝ) * (w : ℝ) < x := by
          have h1 : ¬ (1 ≤ (d : ℝ) * (w : ℝ) / x) := fun hge => heta (eta0_eq_zero_of_one_le hge)
          push_neg at h1
          rwa [div_lt_one hx] at h1
        have h2 : (d : ℝ) * (w : ℝ) = ((d * w : ℕ) : ℝ) := by push_cast; ring
        rw [h2] at hdw
        have h3 : d * w ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx.le).2 hdw.le
        have hw1 : 0 < w := by
          have hlt : (0 : ℝ) < (w : ℝ) := hV0.trans_lt hc.2.1
          exact_mod_cast hlt
        exact hd (Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_mul_of_pos_right d hw1) (by omega : d * w < ⌊x⌋₊ + 1)))
      simp only [hz, tsum_zero])]
    apply Finset.sum_congr rfl
    intro d hd
    rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1)) (fun w hw => by
      have hz : (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
              TaoFivePrimes.expCircle (alpha * d * w) *
              ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) = 0 := by
        by_contra hne
        have hc : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 := by
          by_contra hc2; exact hne (if_neg hc2)
        have heta : TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) ≠ 0 := by
          intro hz2; exact hne (by rw [if_pos hc, hz2]; simp)
        have hdw : (d : ℝ) * (w : ℝ) < x := by
          have h1 : ¬ (1 ≤ (d : ℝ) * (w : ℝ) / x) := fun hge => heta (eta0_eq_zero_of_one_le hge)
          push_neg at h1
          rwa [div_lt_one hx] at h1
        have h2 : (d : ℝ) * (w : ℝ) = ((d * w : ℕ) : ℝ) := by push_cast; ring
        rw [h2] at hdw
        have h3 : d * w ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx.le).2 hdw.le
        have hd1 : 0 < d := by
          have hlt : (0 : ℝ) < (d : ℝ) := hU0.trans_lt hc.1
          exact_mod_cast hlt
        exact hw (Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_mul_of_pos_left w hd1) (by omega : d * w < ⌊x⌋₊ + 1)))
      exact hz)]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hc : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
    · rw [if_pos hc, if_pos hc.2.1, arithmeticRestrictGT_apply, if_pos ((Nat.floor_lt hU0).2 hc.1)]
      rw [eta0VaughanTest_apply, if_pos (Nat.coprime_mul_iff_left.mpr ⟨hc.2.2.1, hc.2.2.2⟩)]
      push_cast
      simp only [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast]
      ring
    · rw [if_neg hc, eta0VaughanTest_apply]
      by_cases hd : U < (d : ℝ)
      · by_cases hw' : V < (w : ℝ)
        · by_cases hodd : (d.Coprime 2) ∧ (w.Coprime 2)
          · exact absurd ⟨hd, hw', hodd.1, hodd.2⟩ hc
          · rw [if_neg (fun h => hodd (Nat.coprime_mul_iff_left.mp h)),
                arithmeticRestrictGT_apply, if_pos ((Nat.floor_lt hU0).2 hd)]
            simp
        · rw [if_neg hw']
          simp
      · rw [arithmeticRestrictGT_apply, if_neg (fun h => hd ((Nat.floor_lt hU0).1 h))]
        simp
  exact hCc
