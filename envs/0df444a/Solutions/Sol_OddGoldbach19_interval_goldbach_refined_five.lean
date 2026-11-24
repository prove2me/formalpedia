-- Prove2me | solution 1 for OddGoldbach19.interval_goldbach_refined_five
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:14:15.239377+00:00
-- url     : https://prove2.me/submissions/ca5c298e-4b99-4f24-9d3d-f48f95833ca5

/- Adapted from public Apache2.0 accepted Prove2Me submission 993546cc-ae39-4daa-a8a3-2781b3db2d70. Refined denominator and sieve coefficient are proved new inputs. -/
import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_OddGoldbach19_interval_reciprocal_weighted_sifted_five
import Theorems.Thm_OddGoldbach19_reciprocal_denominator_five_bounds
import Theorems.Thm_PrimePairSieve_divisor_kernel_comparison
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate

/-! Goldbach analogue of Siebert's bound: `r(s) ≤ 8 C K(s) (s+1)/log²(s+1) + √(s+1)/2 + 2`,
from the platform's proved weighted large-sieve bound for sifted sets, the divisor-kernel
comparison and the base-denominator threshold. The Goldbach set `{p : s - p prime}` is sifted
by `n (n + d)` with `d = 2 s P - s`, `P` the primorial of the sieve level, so that `p ∣ d ↔ p ∣ s`
for every sieving prime `p`. -/

set_option autoImplicit false
open Finset Real

namespace RV27

/-- singular-series weight `K(s) = ∏_{p ∣ s, p > 2} (p-1)/(p-2)`. -/
noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

noncomputable def bfun (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)

noncomputable def gfun (d n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, if p ∣ d then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)

theorem Kf_factor_ge_one (p : ℕ) : (1 : ℝ) ≤ if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  split_ifs with h
  · have : (2 : ℝ) < p := by exact_mod_cast h
    rw [le_div_iff₀ (by linarith)]; linarith
  · exact le_rfl

theorem one_le_Kf (s : ℕ) : 1 ≤ Kf s := by
  unfold Kf
  calc (1 : ℝ) = ∏ p ∈ s.primeFactors, (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => by norm_num) (fun p _ => Kf_factor_ge_one p)

theorem bfun_nonneg (n : ℕ) : 0 ≤ bfun n := by
  unfold bfun
  apply prod_nonneg
  intro p hp
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs with h
  · norm_num
  · have : (3 : ℝ) ≤ p := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    apply div_nonneg (by norm_num); linarith

/-- squarefree numbers `≤ Z` are exactly the divisors of `Z#` that are `≤ Z`. -/
theorem divisors_primorial_filter (Z : ℕ) :
    (primorial Z).divisors.filter (fun n => n ≤ Z) = (Icc 1 Z).filter Squarefree := by
  ext n
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hle⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos hdvd (primorial_pos Z), hle⟩, ?_⟩
    exact (squarefree_primorial Z).squarefree_of_dvd hdvd
  · rintro ⟨⟨h1, hle⟩, hsq⟩
    exact ⟨⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hle), primorial_ne_zero Z⟩, hle⟩

/-- a sum over divisors of `Z#` of a function vanishing above `Z`. -/
theorem sum_divisors_primorial (Z : ℕ) (f : ℕ → ℝ) (hf : ∀ n, Z < n → f n = 0) :
    ∑ n ∈ (primorial Z).divisors, f n = ∑ n ∈ (Icc 1 Z).filter Squarefree, f n := by
  rw [← divisors_primorial_filter, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rfl
  · exact hf n (by omega)

set_option maxHeartbeats 1000000 in
/-- Goldbach analogue of Siebert's bound on an interval `(a, a + L]`, for even `s`. -/
theorem interval_goldbach_main_five (s a L : ℕ) (hs : Even s) (hs0 : 0 < s) (hL : 25600 ≤ L) (hl : 100 ≤ log (L : ℝ)) :
    (((Finset.Ioc a (a + L)).filter (fun p => p.Prime ∧ p < s ∧ (s - p).Prime)).card : ℝ) ≤
      8 * TaoFivePrimes.twinPrimeConstant * Kf s * (L : ℝ) / (log (L : ℝ)*(log (L : ℝ)+5.6)) + 2*√(L : ℝ)/√5 + 2 := by
  set N := L with hNdef
  have hNR : (N : ℝ) = (L : ℝ) := rfl
  have hs1R : (25600 : ℝ) ≤ L := by exact_mod_cast hL
  have hNpos : (0 : ℝ) < N := by rw [hNR]; linarith
  set z : ℝ := √(N : ℝ) / √5 with hz
  have hsq : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hNpos.le
  have hzpos : 0 < z := by rw [hz]; positivity
  have hz1 : 1 ≤ z := by
    rw [hz, le_div_iff₀ (by positivity)]
    simpa using Real.sqrt_le_sqrt (show (5:ℝ) ≤ N by rw [hNR]; linarith)
  have hzN : 5*z^2 = N := by
    rw [hz, div_pow, hsq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
    ring
  set Z := ⌊z⌋₊ with hZ
  have hZz : (Z : ℝ) ≤ z := Nat.floor_le hzpos.le
  have hZ1 : 1 ≤ Z := Nat.le_floor (by norm_num; linarith)
  have hzZ : ∀ n : ℕ, Z < n → z < n := by
    intro n hn
    have h1 : z < (Z : ℝ) + 1 := Nat.lt_floor_add_one z
    have h2 : (Z : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  set P := primorial Z with hP
  have hP1 : 1 ≤ P := primorial_pos Z
  set M := 2 * s * P with hM
  have hsM : s ≤ M := by
    rw [hM]; nlinarith [Nat.zero_le s]
  set d := M - s with hd
  have hd2 : 2 ∣ d := by
    obtain ⟨k, hk⟩ := hs
    have hM2 : 2 ∣ M := ⟨s * P, by rw [hM]; ring⟩
    exact Nat.dvd_sub hM2 ⟨k, by omega⟩
  have hpM : ∀ p, p.Prime → p ≤ Z → p ∣ M := fun p hp hpZ =>
    Dvd.dvd.mul_left ((hp.dvd_primorial_iff).2 hpZ) _
  have hpd : ∀ p, p.Prime → p ≤ Z → p ∣ d → p ∣ s := by
    intro p hp hpZ h
    have h1 := hpM p hp hpZ
    have hdM : d + s = M := by omega
    rw [← hdM] at h1
    exact (Nat.dvd_add_right h).1 h1
  -- the sifted set
  set A := (Ico (a + 1) (a + 1 + N)).filter (fun n : ℕ => n.Prime ∧ z < n ∧ n ≤ s ∧ (s - n).Prime ∧
    z < ((s - n : ℕ) : ℝ)) with hA
  set Q : Finset ℕ+ := (Finset.Icc (1 : ℕ+) (Nat.toPNat' Z)).filter (fun q => Squarefree (q : ℕ))
    with hQ
  have hmemQ : ∀ q : ℕ+, q ∈ Q ↔ (1 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Z) ∧ Squarefree (q : ℕ) := by
    intro q
    rw [hQ, mem_filter, mem_Icc, ← PNat.coe_le_coe, ← PNat.coe_le_coe, Nat.toPNat'_coe,
      if_pos (by omega)]
    simp
  have hQ1 : (1 : ℕ+) ∈ Q := by
    rw [hmemQ]; simp [hZ1]
  have hQz : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z := by
    intro q hq
    rw [hmemQ] at hq
    refine ⟨hq.2, ?_⟩
    have : ((q : ℕ) : ℝ) ≤ Z := by exact_mod_cast hq.1.2
    linarith
  have hAN : A ⊆ Ico (a + 1) (a + 1 + N) := filter_subset _ _
  have hAs : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n * (n + d) := by
    intro q hq n hn p hp hdvd
    rw [hmemQ] at hq
    rw [hA, mem_filter] at hn
    obtain ⟨-, hnp, hzn, hns, hsnp, hzsn⟩ := hn
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpq : p ≤ (q : ℕ) := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    have hpZ : p ≤ Z := hpq.trans hq.1.2
    have hpz : (p : ℝ) ≤ z := by
      have : (p : ℝ) ≤ Z := by exact_mod_cast hpZ
      linarith
    rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpp hnp).1 h
      subst this; linarith
    · have e : n + d = M - (s - n) := by omega
      rw [e] at h
      have h2 : p ∣ s - n := by
        have h1 := hpM p hpp hpZ
        have hsum : M - (s - n) + (s - n) = M := by omega
        rw [← hsum] at h1
        exact (Nat.dvd_add_right h).1 h1
      have := (Nat.prime_dvd_prime_iff_eq hpp hsnp).1 h2
      rw [← this] at hzsn; linarith
  have hsieve := OddGoldbach19.interval_reciprocal_weighted_sifted_five Q hQ1 (a + 1) N d z hz1
    hQz hd2 A hAN hAs
  -- the kernel `F`
  set F : ℕ → ℝ := fun n => if (n : ℝ) ≤ z then 1 / ((N : ℝ) + 5 * n * z) else 0 with hF
  have hFanti : Antitone F := by
    intro a b hab
    simp only [hF]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    split_ifs with h1 h2 h2
    · apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    · linarith
    · positivity
    · exact le_rfl
  have hFvan : ∀ (f : ℕ → ℝ) (n : ℕ), Z < n → f n * F n = 0 := by
    intro f n hn
    have := hzZ n hn
    simp only [hF, if_neg (not_le.2 this), mul_zero]
  set Sq := (Icc 1 Z).filter Squarefree with hSq
  have hQmap : Q.map ⟨PNat.val, PNat.coe_injective⟩ = Sq := by
    ext n
    simp only [mem_map, Function.Embedding.coeFn_mk, hSq, mem_filter, mem_Icc]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (hmemQ q).1 hq
    · rintro h
      refine ⟨⟨n, by omega⟩, (hmemQ _).2 h, rfl⟩
  have hFon : ∀ n ∈ Sq, F n = 1 / ((N : ℝ) + 5 * n * z) := by
    intro n hn
    rw [hSq, mem_filter, mem_Icc] at hn
    have : (n : ℝ) ≤ Z := by exact_mod_cast hn.1.2
    simp only [hF, if_pos (this.trans hZz)]
  -- the sieve sum
  set X := ∑ q ∈ Q, (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) /
      ((N : ℝ) + 5 * ((q : ℕ) : ℝ) * z) with hXdef
  have hX : X = ∑ n ∈ P.divisors, gfun d n * F n := by
    rw [sum_divisors_primorial Z _ (hFvan _), hXdef, ← hSq, ← hQmap, sum_map]
    refine sum_congr rfl fun q hq => ?_
    have hn : (q : ℕ) ∈ Sq := by rw [← hQmap]; exact mem_map_of_mem _ hq
    have e : (⟨PNat.val, PNat.coe_injective⟩ : ℕ+ ↪ ℕ) q = (q : ℕ) := rfl
    rw [e, hFon _ hn, gfun]; ring
  set Bt := ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) with hBt
  have hBt' : Bt = ∑ n ∈ Sq, bfun n / (1 + n / z) := by
    rw [hBt, ← hZ, hSq, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [bfun]
  have hY : ∑ n ∈ P.divisors, bfun n * F n = Bt / N := by
    rw [sum_divisors_primorial Z _ (hFvan _), hBt', sum_div]
    refine sum_congr rfl fun n hn => ?_
    rw [hFon n hn]
    have h1 : (N : ℝ) + 5 * n * z = N * (1 + n / z) := by
      rw [← hzN]; field_simp
    rw [h1]; field_simp
  have hK := PrimePairSieve.divisor_kernel_comparison P d (squarefree_primorial Z) hd2 F hFanti
  have hKp : (∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) ≤ Kf s := by
    rw [← prod_filter, Kf, ← prod_filter]
    apply prod_le_prod_of_subset_of_one_le
    · intro p hp
      rw [mem_filter, Nat.mem_primeFactors] at hp ⊢
      obtain ⟨⟨hpp, hpP, -⟩, h2, hpdv⟩ := hp
      have hpZ := (hpp.dvd_primorial_iff).1 hpP
      exact ⟨⟨hpp, hpd p hpp hpZ hpdv, by omega⟩, h2⟩
    · intro p hp
      have h2 := (mem_filter.1 hp).2.1
      have : (2 : ℝ) < p := by exact_mod_cast h2
      apply div_nonneg (by linarith) (by linarith)
    · intro p hp _
      have h2 := (mem_filter.1 hp).2
      have := Kf_factor_ge_one p
      rwa [if_pos h2] at this
  -- assemble
  obtain ⟨hC1, -, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  set C := TaoFivePrimes.twinPrimeConstant with hCdef
  have hlogN : 0 < log (N : ℝ) := by rw [hNR]; linarith
  set T := (log N*(log N+5.6))/(8*C) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hBT : T ≤ Bt := by
    have hh := (OddGoldbach19.reciprocal_denominator_five_bounds (N : ℝ) hNpos (by rw [hNR]; linarith)).2 (by rwa [hNR])
    change log N*(log N+5.6) ≤ 8*C*Bt at hh
    rw [hTdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hBpos : 0 < Bt := lt_of_lt_of_le hTpos hBT
  have hKs := one_le_Kf s
  have hYX : Bt / N ≤ X * Kf s := by
    rw [← hY, hX]
    have hX0 : 0 ≤ ∑ n ∈ P.divisors, gfun d n * F n := by
      rw [← hX, hXdef]
      apply sum_nonneg; intro q hq
      apply div_nonneg _ (by positivity)
      apply prod_nonneg; intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      split_ifs with h
      · apply div_nonneg (by norm_num); linarith
      · have hp2' : p ≠ 2 := fun h2 => h (h2 ▸ hd2)
        have : (3 : ℝ) ≤ p := by
          have : 3 ≤ p := by omega
          exact_mod_cast this
        apply div_nonneg (by norm_num); linarith
    exact hK.trans (mul_le_mul_of_nonneg_left hKp hX0)
  have hXpos : 0 < X := by
    have : 0 < X * Kf s := lt_of_lt_of_le (by positivity) hYX
    exact pos_of_mul_pos_left this (by linarith)
  have hAcard : (A.card : ℝ) ≤ 8 * C * Kf s * N / (log N*(log N+5.6)) := by
    refine hsieve.trans ?_
    rw [inv_le_iff_one_le_mul₀' hXpos]
    have h1 : T / N ≤ X * Kf s := (div_le_div_of_nonneg_right hBT hNpos.le).trans hYX
    have e : 8 * C * Kf s * N / (log N*(log N+5.6)) = Kf s * N / T := by
      rw [hTdef] <;> field_simp <;> ring
    rw [e]
    rw [div_le_iff₀ hNpos] at h1
    rw [← mul_div_assoc, le_div_iff₀ hTpos]
    nlinarith
  -- the count is at most `|A| + 2 (Z + 1)`
  set R := (Finset.Ioc a (a + L)).filter (fun p => p.Prime ∧ p < s ∧ (s - p).Prime) with hRdef
  have hr : R.card ≤ A.card + (Z + 1) + (Z + 1) := by
    have hsub : R ⊆ A ∪ range (Z + 1) ∪ (range (Z + 1)).image (fun q => s - q) := by
      intro p hp
      rw [hRdef, mem_filter, mem_Ioc] at hp
      obtain ⟨⟨hap, hpa⟩, hpp, hps, hsp⟩ := hp
      by_cases h1 : (p : ℝ) ≤ z
      · apply mem_union_left; apply mem_union_right
        exact mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h1))
      by_cases h2 : ((s - p : ℕ) : ℝ) ≤ z
      · apply mem_union_right
        exact mem_image.2 ⟨s - p, mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h2)), by omega⟩
      · apply mem_union_left; apply mem_union_left
        rw [hA, mem_filter, mem_Ico]
        exact ⟨⟨by omega, by omega⟩, hpp, not_le.1 h1, by omega, hsp, not_le.1 h2⟩
    calc _ ≤ (A ∪ range (Z + 1) ∪ (range (Z + 1)).image (fun q => s - q)).card := card_le_card hsub
      _ ≤ (A ∪ range (Z + 1)).card + ((range (Z + 1)).image (fun q => s - q)).card := card_union_le _ _
      _ ≤ A.card + (range (Z + 1)).card + (range (Z + 1)).card :=
          add_le_add (card_union_le _ _) card_image_le
      _ = _ := by rw [card_range]
  have hr' : (R.card : ℝ) ≤ A.card + 2 * z + 2 := by
    have : (R.card : ℝ) ≤ A.card + (Z + 1) + (Z + 1) := by exact_mod_cast hr
    linarith
  have : 2 * z = 2*√(L : ℝ)/√5 := by rw [hz, hNR]; ring
  linarith

end RV27
theorem solution (s a L : ℕ) (hs : Even s)
    (hs0 : 0 < s) (hL : 25600 ≤ L) (hl : 100 ≤ Real.log (L : ℝ)) :
    (((Finset.Ioc a (a+L)).filter (fun p => p.Prime ∧ p < s ∧ (s-p).Prime)).card : ℝ) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        (∏ p ∈ s.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(L:ℝ)/
        (Real.log (L:ℝ)*(Real.log (L:ℝ)+5.6))+2*Real.sqrt (L:ℝ)/Real.sqrt 5+2 :=
  RV27.interval_goldbach_main_five s a L hs hs0 hL hl
#print axioms solution
