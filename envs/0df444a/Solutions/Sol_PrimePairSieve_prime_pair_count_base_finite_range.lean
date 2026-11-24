-- Prove2me | solution 1 for PrimePairSieve.prime_pair_count_base_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:11:18.092585+00:00
-- url     : https://prove2.me/submissions/fd695d8e-ef2f-4689-a4ae-28b240dad766

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

open scoped BigOperators

namespace PrimePairSieve

namespace WAux

def good210 (r v : ℕ) : Bool :=
  v % 2 == 1 && v % 3 != 0 && (v + r) % 3 != 0 && v % 5 != 0 && (v + r) % 5 != 0 &&
    v % 7 != 0 && (v + r) % 7 != 0

def a210 (r : ℕ) : ℕ := (if r % 3 = 0 then 2 else 1) * (if r % 5 = 0 then 4 else 3) *
  (if r % 7 = 0 then 6 else 5)

def good6 (r v : ℕ) : Bool :=
  v % 2 == 1 && v % 3 != 0 && (v + r) % 3 != 0

def a6 (r : ℕ) : ℕ := if r % 3 = 0 then 2 else 1

set_option maxRecDepth 100000 in
theorem card210 : ∀ r < 210,
    ((Finset.range 210).filter (fun v => good210 r v = true)).card = a210 r := by
  decide +kernel

theorem card6 : ∀ r < 6,
    ((Finset.range 6).filter (fun v => good6 r v = true)).card = a6 r := by
  decide +kernel

theorem count_periodic (m : ℕ) (hm : 0 < m) (g : ℕ → Bool) (x : ℕ) :
    ((Finset.range (x + 1)).filter (fun n => g (n % m) = true)).card ≤
      ((Finset.range m).filter (fun v => g v = true)).card * (x / m + 1) := by
  classical
  have hsub : (Finset.range (x + 1)).filter (fun n => g (n % m) = true) ⊆
      ((Finset.range m).filter (fun v => g v = true)).biUnion
        (fun v => (Finset.range (x + 1)).filter (fun n => n % m = v)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    exact ⟨n % m, ⟨Nat.mod_lt _ hm, hn.2⟩, hn.1, rfl⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro v _
  have : ((Finset.range (x + 1)).filter (fun n => n % m = v)).card ≤
      (Finset.range (x / m + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / m)
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
      simp only at hab
      rw [← Nat.div_add_mod a m, ← Nat.div_add_mod b m, hab, ha.2, hb.2]
  simpa using this

theorem twin_ge_one : 1 ≤ TaoFivePrimes.twinPrimeConstant := by
  unfold TaoFivePrimes.twinPrimeConstant
  have closed : ∀ Q : ℕ, 2 ≤ Q →
      ∏ p ∈ Finset.range (Q + 1), (if 3 ≤ p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) =
        (Q : ℝ) / (2 * ((Q : ℝ) - 1)) := by
    intro Q hQ
    induction Q with
    | zero => omega
    | succ Q ih =>
      rcases Nat.lt_or_ge Q 2 with h | h
      · obtain rfl | rfl : Q = 0 ∨ Q = 1 := by omega
        · omega
        · norm_num [Finset.prod_range_succ]
      · rw [Finset.prod_range_succ, ih h]
        have hQ1 : (2 : ℝ) ≤ Q := by exact_mod_cast h
        rw [if_pos (by omega)]
        push_cast
        rw [show ((Q : ℝ) + 1 - 1) = Q by ring]
        have h1 : (Q : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (Q : ℝ) ≠ 0 := by linarith
        field_simp
        ring
  have half : ∀ Q : ℕ, (1 / 2 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
    intro Q
    have hle : ∏ p ∈ Finset.range (Q + 1), (if 3 ≤ p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤
        TaoFivePrimes.twinPrimePartial Q := by
      unfold TaoFivePrimes.twinPrimePartial
      apply Finset.prod_le_prod
      · intro p _
        split_ifs with h
        · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h
          have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
            rw [div_le_one (by nlinarith)]; nlinarith
          linarith
        · norm_num
      · intro p _
        by_cases hp : Nat.Prime p ∧ 2 < p
        · rw [if_pos hp, if_pos (by omega)]
        · rw [if_neg hp]
          split_ifs with h
          · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
            linarith
          · exact le_rfl
    refine le_trans ?_ hle
    rcases Nat.lt_or_ge Q 2 with h | h
    · obtain rfl | rfl : Q = 0 ∨ Q = 1 := by omega
      · norm_num [Finset.prod_range_succ]
      · norm_num [Finset.prod_range_succ]
    · rw [closed Q h]
      have hQ1 : (2 : ℝ) ≤ Q := by exact_mod_cast h
      rw [le_div_iff₀ (by linarith)]
      linarith
  have : (1 / 2 : ℝ) ≤ sInf (Set.range TaoFivePrimes.twinPrimePartial) :=
    le_csInf (Set.range_nonempty _) (by
      rintro _ ⟨Q, rfl⟩
      exact half Q)
  linarith

noncomputable def Fd (d : ℕ) : ℝ :=
  ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

theorem Fd_bounds (d : ℕ) (hd0 : 0 < d) :
    1 ≤ Fd d ∧ (a6 (d % 6) : ℝ) ≤ Fd d ∧ (a210 (d % 210) : ℝ) ≤ 15 * Fd d := by
  classical
  set f : ℕ → ℝ := fun p => if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 with hf
  have f1 : ∀ p : ℕ, 1 ≤ f p := by
    intro p
    simp only [hf]
    split_ifs with h
    · have : (3 : ℝ) ≤ p := by exact_mod_cast h
      rw [le_div_iff₀ (by linarith)]; linarith
    · exact le_rfl
  set T : Finset ℕ := ({3, 5, 7} : Finset ℕ).filter (· ∣ d) with hT
  have hTsub : T ⊆ Nat.primeFactors d := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Nat.mem_primeFactors]
    refine ⟨?_, hp.2, by omega⟩
    rcases hp.1 with h | h | h <;> subst h
    · exact Nat.prime_three
    · exact Nat.prime_five
    · decide
  have hFT : ∏ p ∈ T, f p ≤ Fd d := by
    unfold Fd
    rw [← Finset.prod_sdiff hTsub]
    have h1 : 1 ≤ ∏ p ∈ Nat.primeFactors d \ T, f p := by
      have := Finset.prod_le_prod (s := Nat.primeFactors d \ T) (f := fun _ => (1 : ℝ)) (g := f)
        (fun _ _ => zero_le_one) (fun p _ => f1 p)
      simpa using this
    have h0 : 0 ≤ ∏ p ∈ T, f p := Finset.prod_nonneg (fun p _ => zero_le_one.trans (f1 p))
    change ∏ p ∈ T, f p ≤ (∏ p ∈ Nat.primeFactors d \ T, f p) * ∏ p ∈ T, f p
    nlinarith
  have key : 1 ≤ ∏ p ∈ T, f p ∧ (a6 (d % 6) : ℝ) ≤ ∏ p ∈ T, f p ∧
      (a210 (d % 210) : ℝ) ≤ 15 * ∏ p ∈ T, f p := by
    have e6 : (d % 6) % 3 = d % 3 := by omega
    have e3 : (d % 210) % 3 = d % 3 := by omega
    have e5 : (d % 210) % 5 = d % 5 := by omega
    have e7 : (d % 210) % 7 = d % 7 := by omega
    simp only [a6, a210, e6, e3, e5, e7]
    by_cases h3 : d % 3 = 0 <;> by_cases h5 : d % 5 = 0 <;> by_cases h7 : d % 7 = 0 <;>
      simp [hT, hf, h3, h5, h7, Nat.dvd_iff_mod_eq_zero, Finset.filter_insert,
        Finset.filter_singleton] <;> norm_num
  refine ⟨key.1.trans hFT, key.2.1.trans hFT, key.2.2.trans (by linarith)⟩

theorem exp_ge (L : ℝ) (hL : 0 ≤ L) : (1 + L / 256) ^ 256 ≤ Real.exp L := by
  have h1 : 1 + L / 256 ≤ Real.exp (L / 256) := by
    have := Real.add_one_le_exp (L / 256); linarith
  have h2 : (1 + L / 256) ^ 256 ≤ Real.exp (L / 256) ^ 256 :=
    pow_le_pow_left₀ (by positivity) h1 256
  rw [← Real.exp_nat_mul] at h2
  have : ((256 : ℕ) : ℝ) * (L / 256) = L := by push_cast; ring
  rwa [this] at h2

theorem seg (α β L x : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx : 0 ≤ x)
    (h0 : 0 ≤ Real.log x) (hL : Real.log x ≤ L) (h : (α + β * x) * L ^ 2 ≤ 8 * x) :
    (α + β * x) * Real.log x ^ 2 ≤ 8 * x := by
  have : Real.log x ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h0 hL 2
  have hab : 0 ≤ α + β * x := by positivity
  nlinarith

theorem logle (x b L : ℝ) (hx : 0 < x) (hxb : x ≤ b) (hL0 : 0 ≤ L)
    (hb : b ≤ (1 + L / 256) ^ 256) : Real.log x ≤ L := by
  rw [Real.log_le_iff_le_exp hx]
  exact hxb.trans (hb.trans (exp_ge L hL0))

theorem small_range (x : ℝ) (h2 : 2 ≤ x) (h : x ≤ 676) :
    (2 + x / 6) * Real.log x ^ 2 ≤ 8 * x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have e : (2 + x / 6) = 2 + (1 / 6) * x := by ring
  rw [e]
  rcases le_or_gt x 13 with h1 | h1
  · exact seg 2 (1/6) 2.6 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 13 2.6 (by linarith) h1 (by norm_num) (by norm_num)) (by nlinarith)
  rcases le_or_gt x 134 with h3 | h3
  · exact seg 2 (1/6) 4.95 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 134 4.95 (by linarith) h3 (by norm_num) (by norm_num)) (by nlinarith)
  · exact seg 2 (1/6) 6.6 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 676 6.6 (by linarith) h (by norm_num) (by norm_num)) (by nlinarith)

theorem large_range (x : ℝ) (h2 : 676 ≤ x) (h : x ≤ 25600) :
    (18 + x / 14) * Real.log x ^ 2 ≤ 8 * x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have e : (18 + x / 14) = 18 + (1 / 14) * x := by ring
  rw [e]
  rcases le_or_gt x 6942 with h1 | h1
  · exact seg 18 (1/14) 9 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 6942 9 (by linarith) h1 (by norm_num) (by norm_num)) (by nlinarith)
  rcases le_or_gt x 25495 with h3 | h3
  · exact seg 18 (1/14) 10.35 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 25495 10.35 (by linarith) h3 (by norm_num) (by norm_num)) (by nlinarith)
  · exact seg 18 (1/14) 10.5 x (by norm_num) (by norm_num) (by linarith) h0
      (logle x 25600 10.5 (by linarith) h (by norm_num) (by norm_num)) (by nlinarith)

end WAux

open WAux in
theorem _root_.solution (x d : ℕ) (hx : 2 ≤ x) (hx0 : x ≤ 25600)
    (hd0 : 0 < d) (hd : 2 ∣ d) :
    (∑ n ∈ Finset.range (x + 1),
      if Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x then (1 : ℝ) else 0) ≤
      8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
        ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  classical
  rw [Finset.sum_boole]
  set A := (Finset.range (x + 1)).filter
    (fun n => Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x) with hA
  change (A.card : ℝ) ≤ _ * Fd d
  have pf : ∀ n ∈ A, ∀ p : ℕ, p.Prime →
      (n % p = 0 → n = p) ∧ ((n + d) % p = 0 → n + d = p) := by
    intro n hn p hp
    simp only [hA, Finset.mem_filter] at hn
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases (Nat.prime_def.mp hn.2.1).2 p (Nat.dvd_of_mod_eq_zero h) with h' | h'
      · exact absurd h' hp.one_lt.ne'
      · exact h'.symm
    · rcases (Nat.prime_def.mp hn.2.2.1).2 p (Nat.dvd_of_mod_eq_zero h) with h' | h'
      · exact absurd h' hp.one_lt.ne'
      · exact h'.symm
  have ge2 : ∀ n ∈ A, 2 ≤ n := by
    intro n hn; simp only [hA, Finset.mem_filter] at hn; exact hn.2.1.two_le
  have p2 := Nat.prime_two
  have p3 := Nat.prime_three
  have p5 := Nat.prime_five
  have p7 : Nat.Prime 7 := by decide
  have b210 : A.card ≤ 3 + a210 (d % 210) * (x / 210 + 1) := by
    have hsub : A ⊆ ({3, 5, 7} : Finset ℕ) ∪
        (Finset.range (x + 1)).filter (fun n => good210 (d % 210) (n % 210) = true) := by
      intro n hn
      have h2 := pf n hn 2 p2
      have h3 := pf n hn 3 p3
      have h5 := pf n hn 5 p5
      have h7 := pf n hn 7 p7
      have hg := ge2 n hn
      have hr : n < x + 1 := by
        simp only [hA, Finset.mem_filter, Finset.mem_range] at hn; exact hn.1
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_range, good210, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
      omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have := count_periodic 210 (by norm_num) (good210 (d % 210)) x
    rw [card210 (d % 210) (Nat.mod_lt _ (by norm_num))] at this
    have : ({3, 5, 7} : Finset ℕ).card = 3 := by decide
    omega
  have b6 : A.card ≤ 1 + a6 (d % 6) * (x / 6 + 1) := by
    have hsub : A ⊆ ({3} : Finset ℕ) ∪
        (Finset.range (x + 1)).filter (fun n => good6 (d % 6) (n % 6) = true) := by
      intro n hn
      have h2 := pf n hn 2 p2
      have h3 := pf n hn 3 p3
      have hg := ge2 n hn
      have hr : n < x + 1 := by
        simp only [hA, Finset.mem_filter, Finset.mem_range] at hn; exact hn.1
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_range, good6, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
      omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have := count_periodic 6 (by norm_num) (good6 (d % 6)) x
    rw [card6 (d % 6) (Nat.mod_lt _ (by norm_num))] at this
    simp only [Finset.card_singleton]
    omega
  obtain ⟨F1, F6, F210⟩ := Fd_bounds d hd0
  have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hxr0 : (x : ℝ) ≤ 25600 := by exact_mod_cast hx0
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hC := twin_ge_one
  have main : ∃ B : ℝ, (A.card : ℝ) ≤ Fd d * B ∧ B * Real.log x ^ 2 ≤ 8 * x := by
    rcases le_or_gt (x : ℝ) 676 with h | h
    · refine ⟨2 + x / 6, ?_, small_range x hxr h⟩
      have c1 : (A.card : ℝ) ≤ 1 + (a6 (d % 6) : ℝ) * (((x / 6 : ℕ) : ℝ) + 1) := by
        exact_mod_cast b6
      have c2 : ((x / 6 : ℕ) : ℝ) ≤ (x : ℝ) / 6 := Nat.cast_div_le
      have c4 : (a6 (d % 6) : ℝ) * (((x / 6 : ℕ) : ℝ) + 1) ≤ Fd d * ((x : ℝ) / 6 + 1) := by
        apply mul_le_mul F6 (by linarith) (by positivity) (by linarith)
      nlinarith
    · refine ⟨18 + x / 14, ?_, large_range x h.le hxr0⟩
      have c1 : (A.card : ℝ) ≤ 3 + (a210 (d % 210) : ℝ) * (((x / 210 : ℕ) : ℝ) + 1) := by
        exact_mod_cast b210
      have c2 : ((x / 210 : ℕ) : ℝ) ≤ (x : ℝ) / 210 := Nat.cast_div_le
      have c4 : (a210 (d % 210) : ℝ) * (((x / 210 : ℕ) : ℝ) + 1) ≤
          15 * Fd d * ((x : ℝ) / 210 + 1) := by
        apply mul_le_mul F210 (by linarith) (by positivity) (by linarith)
      nlinarith
  obtain ⟨B, hB1, hB2⟩ := main
  have hB3 : B ≤ 8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / Real.log x ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc (A.card : ℝ) ≤ Fd d * B := hB1
    _ ≤ Fd d * (8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_left hB3 (by linarith)
    _ = _ := by ring

end PrimePairSieve

#print axioms solution
