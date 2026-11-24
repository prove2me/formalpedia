-- Prove2me | solution 1 for TaoFivePrimes.typeIExpansion_three_bilinear_sums
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T09:20:18.519184+00:00
-- url     : https://prove2.me/submissions/6cec28ac-6082-4cbe-82b6-cbef9da0de9a

import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius BigOperators
open ArithmeticFunction Finset
namespace TaoFivePrimes
theorem eta0_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : eta0 y = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * y) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * y)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * y))))
  rw [max_eq_left hcut, mul_zero]
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
theorem eta0VaughanTypeISum_expansion
    (x alpha U V : ℝ) (hx : 0 < x) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V =
      (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((ArithmeticFunction.log m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      - (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      + (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * w)) := by
  classical
  have htest : ∀ n, ⌊x⌋₊ + 1 ≤ n → TaoFivePrimes.eta0VaughanTest x alpha n = 0 :=
    fun n hn => eta0VaughanTest_eq_zero_of_big hx hn
  let ML : ArithmeticFunction ℝ := TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ)
  let LL : ArithmeticFunction ℝ := TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt
  let MG : ArithmeticFunction ℝ := TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ)
  let H : ArithmeticFunction ℝ := TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊
  let Z : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hVT : TaoFivePrimes.vaughanTypeIPart ⌊U⌋₊ ⌊V⌋₊ =
      ML * ArithmeticFunction.log - ML * LL * Z + MG * H := by
    simp only [TaoFivePrimes.vaughanTypeIPart, ML, LL, MG, H, Z]
  have h1 : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((ML * ArithmeticFunction.log) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
      = ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
          ((ML d : ℝ) : ℂ) * ((ArithmeticFunction.log m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m) :=
    sum_dirichlet_pairing' ML ArithmeticFunction.log
      (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1) htest
  have h2 : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((ML * LL * Z) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
      = ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
          (((ML * LL) d : ℝ) : ℂ) * ((Z m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m) :=
    sum_dirichlet_pairing' (ML * LL) Z
      (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1) htest
  have h3 : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((MG * H) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
      = ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
          ((MG d : ℝ) : ℂ) * ((H w : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * w) :=
    sum_dirichlet_pairing' MG H
      (TaoFivePrimes.eta0VaughanTest x alpha) (⌊x⌋₊ + 1) htest
  have hsplit : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((TaoFivePrimes.vaughanTypeIPart ⌊U⌋₊ ⌊V⌋₊) n : ℝ) : ℂ) *
          TaoFivePrimes.eta0VaughanTest x alpha n)
      = (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ML * ArithmeticFunction.log) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
        - (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ML * LL * Z) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
        + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((MG * H) n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hVT]
    simp only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg]
    push_cast
    ring
  unfold TaoFivePrimes.eta0VaughanTypeISum TaoFivePrimes.arithmeticWeightedSum
  rw [hsplit, h1, h2, h3]
end TaoFivePrimes
open TaoFivePrimes
theorem solution (x alpha U V : ℝ) (hx : 0 < x) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V =
      (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((ArithmeticFunction.log m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      - (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      + (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * w)) :=
  TaoFivePrimes.eta0VaughanTypeISum_expansion x alpha U V hx
