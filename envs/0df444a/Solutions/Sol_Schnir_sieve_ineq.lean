-- Prove2me | solution 1 for Schnir.sieve_ineq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:57:17.336328+00:00
-- url     : https://prove2.me/submissions/2b627e78-3491-43ae-8173-bc3709ad3a46

import Mathlib
import Definitions.Def_Schnir_defs

open Finset Real

namespace Schnir

theorem sieve_rho_le_two (s p : ℕ) : rho s p ≤ 2 := by unfold rho; split_ifs <;> omega
theorem sieve_one_le_rho (s p : ℕ) : 1 ≤ rho s p := by unfold rho; split_ifs <;> omega

theorem sieve_rho_lt (s p : ℕ) (hs : 2 ∣ s) (hp : p.Prime) : rho s p < p := by
  unfold rho
  rcases eq_or_ne p 2 with rfl | h2
  · simp [hs]
  · have := hp.two_le
    split_ifs <;> omega

/-- the sieve density `ν(d) = ρ(d)/d` -/
noncomputable def sieve_nu (s : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (rho s p : ℝ) / p)

theorem sieve_nu_prime (s p : ℕ) (hp : p.Prime) : sieve_nu s p = (rho s p : ℝ) / p := by
  simp [sieve_nu, hp.ne_zero, hp.primeFactors]

noncomputable def sieve_BS (s : ℕ) (hs : 2 ∣ s) (N : ℕ) : BoundingSieve where
  support := (Icc 1 s).image (fun a => a * (s - a))
  prodPrimes := primorial N
  prodPrimes_squarefree := squarefree_primorial N
  weights n := (#{a ∈ Icc 1 s | a * (s - a) = n} : ℝ)
  weights_nonneg n := by positivity
  totalMass := s
  nu := sieve_nu s
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp _ := by
    rw [sieve_nu_prime s p hp]
    have := sieve_one_le_rho s p
    have := hp.pos
    positivity
  nu_lt_one_of_prime p hp _ := by
    rw [sieve_nu_prime s p hp, div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast sieve_rho_lt s p hs hp


/-- number of roots of `x (s - x) = 0` in `ZMod d` -/
noncomputable def sieve_R (s d : ℕ) : ℕ := Nat.card {x : ZMod d // x * ((s : ZMod d) - x) = 0}

theorem sieve_R_mul (s m n : ℕ) (h : m.Coprime n) :
    sieve_R s (m * n) = sieve_R s m * sieve_R s n := by
  unfold sieve_R
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  refine (Equiv.subtypeEquiv e.toEquiv ?_).trans (Equiv.subtypeProdEquivProd)
  intro x
  have : e (x * ((s : ZMod (m * n)) - x)) = (e x) * ((s : ZMod m × ZMod n) - e x) := by
    simp [map_mul, map_sub, map_natCast]
  rw [← map_eq_zero_iff e e.injective, this]
  simp [Prod.ext_iff]

theorem sieve_R_prime (s p : ℕ) (hp : p.Prime) : sieve_R s p = rho s p := by
  have := Fact.mk hp
  unfold sieve_R
  have : {x : ZMod p // x * ((s : ZMod p) - x) = 0} = {x : ZMod p // x ∈ ({0, (s : ZMod p)} : Finset (ZMod p))} := by
    congr 1; ext x
    simp [mul_eq_zero, sub_eq_zero, eq_comm]
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold rho
  by_cases hs : p ∣ s
  · have : (s : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hs
    simp [this, hs]
  · have : (s : ZMod p) ≠ 0 := fun h => hs ((ZMod.natCast_eq_zero_iff _ _).1 h)
    rw [Finset.card_pair this.symm]
    simp [hs]

theorem sieve_R_one (s : ℕ) : sieve_R s 1 = 1 := by
  unfold sieve_R
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

theorem sieve_R_prod (s : ℕ) (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    sieve_R s (∏ p ∈ t, p) = ∏ p ∈ t, rho s p := by
  induction t using Finset.induction_on with
  | empty => simp [sieve_R_one]
  | insert a t ha ih =>
    rw [prod_insert ha, prod_insert ha, sieve_R_mul, sieve_R_prime s a (ht a (by simp)),
      ih (fun p hp => ht p (by simp [hp]))]
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes (ht a (by simp)) (ht q (by simp [hq]))).2 (by rintro rfl; exact ha hq)

theorem sieve_R_squarefree (s d : ℕ) (hd : Squarefree d) :
    sieve_R s d = ∏ p ∈ d.primeFactors, rho s p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact sieve_R_prod s _ (fun p hp => Nat.prime_of_mem_primeFactors hp)


theorem sieve_count_residue (s d v : ℕ) (hd : 0 < d) :
    |(#{a ∈ Icc 1 s | a ≡ v [MOD d]} : ℝ) - s / d| ≤ 1 := by
  have key := Nat.Ioc_filter_modEq_card 0 s hd v
  have hI : Ioc 0 s = Icc 1 s := by ext a; simp; omega
  rw [hI] at key
  set c : ℕ := #{a ∈ Icc 1 s | a ≡ v [MOD d]}
  set x : ℚ := ((s : ℚ) - v) / d
  set y : ℚ := (((0:ℕ) : ℚ) - v) / d
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hxy : x - y = s / d := by simp only [x, y]; field_simp; ring
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hnn : 0 ≤ ⌊x⌋ - ⌊y⌋ := by
    have : ((-1 : ℤ) : ℚ) < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) := by
      push_cast
      have : (0 : ℚ) ≤ s / d := by positivity
      linarith
    have := Int.cast_lt.1 this
    omega
  rw [max_eq_left hnn] at key
  have hq : |(c : ℚ) - s / d| ≤ 1 := by
    have : (c : ℚ) = ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) := by exact_mod_cast key
    rw [this, abs_le]; push_cast
    constructor <;> linarith
  have : |(c : ℝ) - s / d| = ((|(c : ℚ) - s / d| : ℚ) : ℝ) := by push_cast; rfl
  rw [this]
  exact_mod_cast hq


theorem sieve_multSum (s : ℕ) (hs : 2 ∣ s) (N d : ℕ) :
    (sieve_BS s hs N).multSum d = #{a ∈ Icc 1 s | d ∣ a * (s - a)} := by
  simp only [BoundingSieve.multSum, sieve_BS]
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 s) (t := (Icc 1 s).image (fun a => a * (s - a)))
    (g := fun a => a * (s - a)) (fun a ha => mem_image_of_mem _ ha)]
  apply sum_congr rfl
  intro n _
  split_ifs with h
  · rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_filter]
    apply sum_congr rfl
    intro a _
    split_ifs with h1 h2 <;> simp_all
  · symm
    apply sum_eq_zero
    intro a ha
    rw [(mem_filter.1 ha).2]
    simp [h]

theorem sieve_count_dvd (s d : ℕ) (hd : d ≠ 0) :
    |(#{a ∈ Icc 1 s | d ∣ a * (s - a)} : ℝ) - s * (sieve_R s d) / d| ≤ sieve_R s d := by
  have : NeZero d := ⟨hd⟩
  set t : Finset (ZMod d) := univ.filter (fun x => x * ((s : ZMod d) - x) = 0) with ht
  have hR : sieve_R s d = #t := by
    unfold sieve_R
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmem : ∀ a ∈ Icc 1 s, d ∣ a * (s - a) ↔ (a : ZMod d) ∈ t := by
    intro a ha
    have has : a ≤ s := (mem_Icc.1 ha).2
    rw [ht, mem_filter, ← ZMod.natCast_eq_zero_iff]
    push_cast [has]
    simp
  have h1 : #{a ∈ Icc 1 s | d ∣ a * (s - a)} = ∑ r ∈ t, #{a ∈ Icc 1 s | a ≡ r.val [MOD d]} := by
    rw [card_eq_sum_card_fiberwise (f := fun a : ℕ => (a : ZMod d)) (t := t) ?_]
    · apply sum_congr rfl
      intro r hr
      congr 1
      ext a
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨ha, -⟩, rfl⟩
        exact ⟨ha, by rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]⟩
      · rintro ⟨ha, hm⟩
        have : (a : ZMod d) = r := by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hm; exact hm
        exact ⟨⟨ha, (hmem a ha).2 (this ▸ hr)⟩, this⟩
    · intro a ha
      rw [coe_filter] at ha
      exact (hmem a ha.1).1 ha.2
  rw [h1, hR, Nat.cast_sum]
  have : (s : ℝ) * (#t : ℕ) / d = ∑ r ∈ t, (s : ℝ) / d := by
    rw [sum_const, nsmul_eq_mul]; ring
  rw [this, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ((#t : ℕ) : ℝ) = ∑ r ∈ t, (1 : ℝ) := by simp
  rw [this]
  exact sum_le_sum (fun r _ => sieve_count_residue s d r.val (Nat.pos_of_ne_zero hd))

theorem sieve_rem_le (s : ℕ) (hs : 2 ∣ s) (N d : ℕ) (hd : d ∣ primorial N) :
    |(sieve_BS s hs N).rem d| ≤ ∏ p ∈ d.primeFactors, (rho s p : ℝ) := by
  have hsq : Squarefree d := (squarefree_primorial N).squarefree_of_dvd hd
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hnu : (sieve_BS s hs N).nu d = (sieve_R s d : ℝ) / d := by
    simp only [sieve_BS, sieve_nu, ArithmeticFunction.prodPrimeFactors_apply hd0]
    rw [sieve_R_squarefree s d hsq, prod_div_distrib]
    push_cast
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  simp only [BoundingSieve.rem]
  rw [sieve_multSum, hnu]
  have := sieve_count_dvd s d hd0
  rw [sieve_R_squarefree s d hsq] at this ⊢
  push_cast at this ⊢
  simp only [sieve_BS]
  convert this using 2
  ring

theorem sieve_BS_prodPrimes (s : ℕ) (hs : 2 ∣ s) (N : ℕ) :
    (sieve_BS s hs N).prodPrimes = primorial N := rfl
theorem sieve_BS_support (s : ℕ) (hs : 2 ∣ s) (N : ℕ) :
    (sieve_BS s hs N).support = (Icc 1 s).image (fun a => a * (s - a)) := rfl
theorem sieve_BS_weights (s : ℕ) (hs : 2 ∣ s) (N n : ℕ) :
    (sieve_BS s hs N).weights n = (#{a ∈ Icc 1 s | a * (s - a) = n} : ℝ) := rfl
theorem sieve_BS_nu (s : ℕ) (hs : 2 ∣ s) (N : ℕ) :
    (sieve_BS s hs N).nu = sieve_nu s := rfl
theorem sieve_BS_totalMass (s : ℕ) (hs : 2 ∣ s) (N : ℕ) :
    (sieve_BS s hs N).totalMass = s := rfl

theorem sieve_siftedSum (s : ℕ) (hs : 2 ∣ s) (z : ℝ) :
    (sieve_BS s hs ⌊z⌋₊).siftedSum = S s z := by
  rw [BoundingSieve.siftedSum, sieve_BS_prodPrimes, sieve_BS_support]
  simp only [sieve_BS_weights, S]
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 s) (t := (Icc 1 s).image (fun a => a * (s - a)))
    (g := fun a => a * (s - a)) (fun a ha => mem_image_of_mem _ ha)]
  apply sum_congr rfl
  intro n _
  have hiff : Nat.Coprime (primorial ⌊z⌋₊) n ↔
      ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ n := by
    rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd]
    push Not
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      exact ⟨p, mem_range.2 (Nat.lt_succ_of_le ((hp.dvd_primorial_iff).1 h1)), hp, h2⟩
    · rintro ⟨p, h1, hp, h2⟩
      exact ⟨p, hp, (hp.dvd_primorial_iff).2 (Nat.le_of_lt_succ (mem_range.1 h1)), h2⟩
  by_cases hC : Nat.Coprime (primorial ⌊z⌋₊) n
  · rw [if_pos hC, card_eq_sum_ones, Nat.cast_sum]
    apply sum_congr rfl
    intro a ha
    rw [if_pos (by rw [(mem_filter.1 ha).2]; exact hiff.1 hC)]
  · rw [if_neg hC]; symm; apply sum_eq_zero; intro a ha
    rw [if_neg (by rw [(mem_filter.1 ha).2]; exact fun h => hC (hiff.2 h))]

theorem sieve_sum_moebius_filter (m l : ℕ) (hm : Squarefree m) :
    ∑ d ∈ m.divisors with l ∣ d, (ArithmeticFunction.moebius d : ℝ) =
      if l = m then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  have hm0 : m ≠ 0 := hm.ne_zero
  by_cases hlm : l ∣ m
  · obtain ⟨k, rfl⟩ := hlm
    have hl0 : l ≠ 0 := left_ne_zero_of_mul hm0
    have hk0 : k ≠ 0 := right_ne_zero_of_mul hm0
    have hcop : Nat.Coprime l k := Nat.coprime_of_squarefree_mul hm
    have himg : {d ∈ (l * k).divisors | l ∣ d} = k.divisors.image (fun e => l * e) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨⟨hd, -⟩, e, rfl⟩
        exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hl0) hd, hk0⟩, rfl⟩
      · rintro ⟨e, ⟨he, -⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left l he, hm0⟩, dvd_mul_right _ _⟩
    rw [himg, sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) hab)]
    have : ∀ e ∈ k.divisors, (ArithmeticFunction.moebius (l * e) : ℝ) =
        ArithmeticFunction.moebius l * ArithmeticFunction.moebius e := by
      intro e he
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors he))]
      push_cast; ring
    rw [sum_congr rfl this, ← mul_sum]
    have hz : ∑ e ∈ k.divisors, (ArithmeticFunction.moebius e : ℝ) = if k = 1 then 1 else 0 := by
      have := congrArg (fun f : ArithmeticFunction ℝ => f k)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
      simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
      rw [← this]
      simp
    rw [hz]
    by_cases hk : k = 1
    · simp [hk]
    · have : l ≠ l * k := by
        intro h; apply hk
        exact (Nat.mul_eq_left hl0).1 h.symm
      simp [hk, this]
  · have hne : l ≠ m := by rintro rfl; exact hlm dvd_rfl
    rw [if_neg hne]
    apply sum_eq_zero
    intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) hlm
    

open scoped ArithmeticFunction.Moebius in
/-- Selberg's weights at level `N`. -/
noncomputable def sieve_w (B : BoundingSieve) (N : ℕ) (d : ℕ) : ℝ :=
  if d ≤ N then
    (μ d : ℝ) / (B.nu d * ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) *
      ∑ m ∈ B.prodPrimes.divisors with d ∣ m ∧ m ≤ N, B.selbergTerms m
  else 0

open scoped ArithmeticFunction.Moebius in
theorem sieve_nu_mul_w (B : BoundingSieve) (N d : ℕ) (hd : d ∈ B.prodPrimes.divisors) :
    B.nu d * sieve_w B N d = (μ d : ℝ) / (∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) *
      ∑ m ∈ B.prodPrimes.divisors with d ∣ m ∧ m ≤ N, B.selbergTerms m := by
  have hnu : B.nu d ≠ 0 := BoundingSieve.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
  unfold sieve_w
  split_ifs with h
  · rw [← mul_assoc, mul_div_assoc', mul_div_mul_left _ _ hnu]
  · rw [mul_zero, eq_comm]
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro m hm
    rw [mem_filter] at hm
    obtain ⟨hm, hdm, hmN⟩ := hm
    exfalso
    have : m ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hm)
    exact h ((Nat.le_of_dvd (Nat.pos_of_ne_zero this) hdm).trans hmN)


open scoped ArithmeticFunction.Moebius in
theorem sieve_inner (B : BoundingSieve) (N l : ℕ) (hl : l ∈ B.prodPrimes.divisors) :
    ∑ d ∈ B.prodPrimes.divisors, (if l ∣ d then B.nu d * sieve_w B N d else 0) =
      if l ≤ N then (μ l : ℝ) * B.selbergTerms l /
        (∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) else 0 := by
  set D := B.prodPrimes.divisors with hD
  set Gd := ∑ l ∈ D with l ≤ N, B.selbergTerms l with hGd
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  calc ∑ d ∈ D, (if l ∣ d then B.nu d * sieve_w B N d else 0)
      = ∑ d ∈ D, ∑ m ∈ D,
          (if l ∣ d ∧ d ∣ m ∧ m ≤ N then (μ d : ℝ) / Gd * B.selbergTerms m else 0) := by
        apply sum_congr rfl; intro d hd
        by_cases hld : l ∣ d
        · rw [if_pos hld, sieve_nu_mul_w B N d hd, mul_sum, sum_filter]
          apply sum_congr rfl; intro m _
          by_cases h2 : d ∣ m ∧ m ≤ N
          · rw [if_pos h2, if_pos ⟨hld, h2⟩]
          · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        · rw [if_neg hld]; symm; apply sum_eq_zero; intro m _
          rw [if_neg (fun h => hld h.1)]
    _ = ∑ m ∈ D, ∑ d ∈ D,
          (if l ∣ d ∧ d ∣ m ∧ m ≤ N then (μ d : ℝ) / Gd * B.selbergTerms m else 0) := sum_comm
    _ = ∑ m ∈ D, (if m ≤ N then B.selbergTerms m / Gd *
          ∑ d ∈ m.divisors with l ∣ d, (μ d : ℝ) else 0) := by
        apply sum_congr rfl; intro m hm
        by_cases hmN : m ≤ N
        · rw [if_pos hmN, mul_sum, ← Nat.divisors_filter_dvd_of_dvd hP (Nat.dvd_of_mem_divisors hm),
            filter_filter, sum_filter]
          apply sum_congr rfl; intro d _
          by_cases h : l ∣ d ∧ d ∣ m
          · rw [if_pos ⟨h.1, h.2, hmN⟩, if_pos ⟨h.2, h.1⟩]; ring
          · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
        · rw [if_neg hmN]; apply sum_eq_zero; intro d _
          rw [if_neg (fun h => hmN h.2.2)]
    _ = ∑ m ∈ D, (if l = m then (if l ≤ N then (μ l : ℝ) * B.selbergTerms l / Gd else 0)
          else 0) := by
        apply sum_congr rfl; intro m hm
        rw [sieve_sum_moebius_filter m l
          (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hm)]
        by_cases hlm : l = m
        · subst hlm; simp only [if_true]
          split_ifs <;> ring
        · simp [hlm]
    _ = _ := by rw [sum_ite_eq D l]; rw [if_pos hl]


theorem sieve_Gd_pos (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) :
    0 < ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l := by
  apply sum_pos'
  · intro l hl
    exact (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.1 hl).1)).le
  · refine ⟨1, mem_filter.2 ⟨Nat.one_mem_divisors.2 BoundingSieve.prodPrimes_ne_zero, hN⟩, ?_⟩
    exact BoundingSieve.selbergTerms_pos (one_dvd _)

theorem sieve_w_one (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) : sieve_w B N 1 = 1 := by
  have := sieve_Gd_pos B N hN
  unfold sieve_w
  rw [if_pos hN]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, B.nu_mult.map_one, one_mul,
    one_dvd, true_and]
  field_simp

theorem sieve_mainSum (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) :
    B.mainSum (BoundingSieve.lambdaSquared (sieve_w B N)) =
      1 / ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l := by
  have hG := sieve_Gd_pos B N hN
  set Gd := ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l with hGd
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  rw [sum_congr rfl (fun l hl => by rw [sieve_inner B N l hl])]
  have : ∀ l ∈ B.prodPrimes.divisors, (B.selbergTerms l)⁻¹ *
      (if l ≤ N then (ArithmeticFunction.moebius l : ℝ) * B.selbergTerms l / Gd else 0) ^ 2 =
      if l ≤ N then B.selbergTerms l / Gd ^ 2 else 0 := by
    intro l hl
    have hpos := BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    have hmu : ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hl)
    split_ifs
    · field_simp
      exact hmu
    · simp
  rw [sum_congr rfl this, ← sum_filter, ← sum_div, ← hGd]
  field_simp


theorem sieve_w_abs_le (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) (d : ℕ)
    (hd : d ∈ B.prodPrimes.divisors) : |sieve_w B N d| ≤ 1 := by
  have hG := sieve_Gd_pos B N hN
  set D := B.prodPrimes.divisors with hD
  set Gd := ∑ l ∈ D with l ≤ N, B.selbergTerms l with hGd
  have hdP : d ∣ B.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hnu : 0 < B.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
  have hmult := BoundingSieve.selbergTerms_isMultiplicative (s := B)
  unfold sieve_w
  split_ifs with hdN
  swap
  · simp
  set M := {m ∈ D | d ∣ m ∧ m ≤ N} with hM
  set Bd := {b ∈ D | b ∣ d} with hBd
  have hMmem : ∀ m ∈ M, m ∈ D ∧ d ∣ m ∧ m ≤ N := fun m hm => by
    simpa [hM] using hm
  have hBmem : ∀ b ∈ Bd, b ∈ D ∧ b ∣ d := fun b hb => by
    simpa [hBd] using hb
  -- decomposition m = d * k with k coprime to d
  have hdec : ∀ m ∈ M, d * (m / d) = m ∧ Nat.Coprime d (m / d) := by
    intro m hm
    obtain ⟨hmD, hdm, -⟩ := hMmem m hm
    have e : d * (m / d) = m := Nat.mul_div_cancel' hdm
    refine ⟨e, Nat.coprime_of_squarefree_mul ?_⟩
    rw [e]; exact BoundingSieve.squarefree_of_mem_divisors_prodPrimes hmD
  have key : ∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹ ≤ Gd := by
    calc ∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹
        = ∑ m ∈ M, ∑ b ∈ Bd, B.selbergTerms (b * (m / d)) := by
          apply sum_congr rfl; intro m hm
          obtain ⟨e, hcop⟩ := hdec m hm
          conv_lhs => rw [← e]
          rw [hmult.map_mul_of_coprime hcop, mul_right_comm,
            ← BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP,
            ← sum_filter, sum_mul]
          apply sum_congr rfl; intro b hb
          rw [hmult.map_mul_of_coprime (hcop.coprime_dvd_left (hBmem b hb).2)]
      _ = ∑ x ∈ M ×ˢ Bd, B.selbergTerms (x.2 * (x.1 / d)) := by rw [sum_product]
      _ = ∑ l ∈ (M ×ˢ Bd).image (fun x => x.2 * (x.1 / d)), B.selbergTerms l := by
          rw [sum_image]
          rintro ⟨m1, b1⟩ h1 ⟨m2, b2⟩ h2 heq
          simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
          simp only at heq
          obtain ⟨e1, c1⟩ := hdec m1 h1.1
          obtain ⟨e2, c2⟩ := hdec m2 h2.1
          have hb1 := (hBmem b1 h1.2).2
          have hb2 := (hBmem b2 h2.2).2
          have g1 : Nat.gcd (b1 * (m1 / d)) d = b1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel _ c1.symm, Nat.gcd_eq_left hb1]
          have g2 : Nat.gcd (b2 * (m2 / d)) d = b2 := by
            rw [Nat.Coprime.gcd_mul_right_cancel _ c2.symm, Nat.gcd_eq_left hb2]
          have hbb : b1 = b2 := by rw [← g1, ← g2, heq]
          subst hbb
          have hb0 : 0 < b1 := Nat.pos_of_dvd_of_pos hb1 hd0
          have hk : m1 / d = m2 / d := Nat.eq_of_mul_eq_mul_left hb0 heq
          have : m1 = m2 := by rw [← e1, ← e2, hk]
          rw [this]
      _ ≤ Gd := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro l hl
            rw [mem_image] at hl
            obtain ⟨⟨m, b⟩, hx, rfl⟩ := hl
            rw [mem_product] at hx
            obtain ⟨hmD, hdm, hmN⟩ := hMmem m hx.1
            obtain ⟨e, -⟩ := hdec m hx.1
            have hb := (hBmem b hx.2).2
            have hdiv : b * (m / d) ∣ m := by
              conv_rhs => rw [← e]
              exact Nat.mul_dvd_mul_right hb _
            have hm0 : 0 < m := Nat.pos_of_mem_divisors hmD
            rw [mem_filter]
            refine ⟨Nat.mem_divisors.2 ⟨hdiv.trans (Nat.dvd_of_mem_divisors hmD), hP⟩, ?_⟩
            exact (Nat.le_of_dvd hm0 hdiv).trans hmN
          · intro l hl _
            exact (BoundingSieve.selbergTerms_pos
              (Nat.dvd_of_mem_divisors (mem_filter.1 hl).1)).le
  have hSnn : 0 ≤ ∑ m ∈ M, B.selbergTerms m := sum_nonneg (fun m hm =>
    (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (hMmem m hm).1)).le)
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_mul, abs_div, abs_of_pos (mul_pos hnu hG), abs_of_nonneg hSnn]
  calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (B.nu d * Gd) * ∑ m ∈ M, B.selbergTerms m
      ≤ 1 / (B.nu d * Gd) * ∑ m ∈ M, B.selbergTerms m :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmu (mul_pos hnu hG).le) hSnn
    _ = (∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹) / Gd := by
        rw [← sum_mul]; field_simp
    _ ≤ Gd / Gd := div_le_div_of_nonneg_right key hG.le
    _ = 1 := div_self hG.ne'


theorem sieve_errSum_le (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) (R : ℕ → ℝ)
    (hR0 : ∀ d ∈ B.prodPrimes.divisors, 0 ≤ R d)
    (hrem : ∀ d ∈ B.prodPrimes.divisors, |B.rem d| ≤ R d)
    (hRl : ∀ a ∈ B.prodPrimes.divisors, ∀ b ∈ B.prodPrimes.divisors,
      R (Nat.lcm a b) ≤ R a * R b) :
    B.errSum (BoundingSieve.lambdaSquared (sieve_w B N)) ≤
      (∑ d ∈ B.prodPrimes.divisors with d ≤ N, R d) ^ 2 := by
  set D := B.prodPrimes.divisors with hD
  set w := sieve_w B N with hw
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hsub : ∀ d ∈ D, d.divisors ⊆ D := fun d hd =>
    Nat.divisors_subset_of_dvd hP (Nat.dvd_of_mem_divisors hd)
  have hlcm : ∀ a ∈ D, ∀ b ∈ D, Nat.lcm a b ∈ D := fun a ha b hb =>
    Nat.mem_divisors.2 ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb), hP⟩
  have hwabs : ∀ d ∈ D, |w d| ≤ 1 := fun d hd => sieve_w_abs_le B N hN d hd
  have hwN : ∀ d, ¬ d ≤ N → w d = 0 := fun d hd => by simp [hw, sieve_w, hd]
  unfold BoundingSieve.errSum
  calc ∑ d ∈ D, |BoundingSieve.lambdaSquared w d| * |B.rem d|
      ≤ ∑ d ∈ D, (∑ d1 ∈ D, ∑ d2 ∈ D,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) * R d := by
        apply sum_le_sum; intro d hd
        apply mul_le_mul _ (hrem d hd) (abs_nonneg _) (sum_nonneg fun _ _ =>
          sum_nonneg fun _ _ => by positivity)
        unfold BoundingSieve.lambdaSquared
        refine (abs_sum_le_sum_abs _ _).trans ?_
        refine (sum_le_sum fun d1 _ => abs_sum_le_sum_abs _ _).trans ?_
        have e : ∀ d1 d2, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| =
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
          intro d1 d2; split_ifs <;> simp [abs_mul]
        simp only [e]
        refine (sum_le_sum fun d1 _ => sum_le_sum_of_subset_of_nonneg (hsub d hd)
          (fun _ _ _ => by positivity)).trans ?_
        apply sum_le_sum_of_subset_of_nonneg (hsub d hd)
        intro _ _ _; exact sum_nonneg fun _ _ => by positivity
    _ = ∑ d1 ∈ D, ∑ d2 ∈ D, |w d1| * |w d2| * R (Nat.lcm d1 d2) := by
        simp_rw [sum_mul, ite_mul, zero_mul]
        rw [sum_comm]
        apply sum_congr rfl; intro d1 hd1
        rw [sum_comm]
        apply sum_congr rfl; intro d2 hd2
        rw [sum_ite_eq', if_pos (hlcm d1 hd1 d2 hd2)]
    _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, (if d1 ≤ N then R d1 else 0) * (if d2 ≤ N then R d2 else 0) := by
        apply sum_le_sum; intro d1 hd1
        apply sum_le_sum; intro d2 hd2
        by_cases h1 : d1 ≤ N
        · by_cases h2 : d2 ≤ N
          · rw [if_pos h1, if_pos h2]
            calc |w d1| * |w d2| * R (Nat.lcm d1 d2) ≤ 1 * 1 * R (Nat.lcm d1 d2) := by
                  apply mul_le_mul_of_nonneg_right _ (hR0 _ (hlcm d1 hd1 d2 hd2))
                  exact mul_le_mul (hwabs d1 hd1) (hwabs d2 hd2) (abs_nonneg _) zero_le_one
              _ ≤ R d1 * R d2 := by rw [one_mul, one_mul]; exact hRl d1 hd1 d2 hd2
          · rw [hwN d2 h2]; simp [h2]
        · rw [hwN d1 h1]; simp [h1]
    _ = (∑ d ∈ D with d ≤ N, R d) ^ 2 := by
        rw [sq, sum_filter, sum_mul_sum]


theorem sieve_selbergTerms_eq (s : ℕ) (hs : 2 ∣ s) (N d : ℕ) (hd : d ≠ 0) :
    (sieve_BS s hs N).selbergTerms d = hfun s d := by
  rw [BoundingSieve.selbergTerms_apply, sieve_BS_nu, sieve_nu,
    ArithmeticFunction.prodPrimeFactors_apply hd, ← prod_mul_distrib, hfun]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [← sieve_nu, sieve_nu_prime s p hpp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hlt : (rho s p : ℝ) < p := by exact_mod_cast sieve_rho_lt s p hs hpp
  have hpr : (p : ℝ) - rho s p ≠ 0 := by linarith
  rw [one_sub_div hp0, inv_div]
  field_simp

theorem sieve_G_eq (s : ℕ) (hs : 2 ∣ s) (z : ℝ) :
    G s z = ∑ l ∈ (sieve_BS s hs ⌊z⌋₊).prodPrimes.divisors with l ≤ ⌊z⌋₊,
      (sieve_BS s hs ⌊z⌋₊).selbergTerms l := by
  unfold G
  have hset : (Icc 1 ⌊z⌋₊).filter Squarefree =
      (sieve_BS s hs ⌊z⌋₊).prodPrimes.divisors.filter (· ≤ ⌊z⌋₊) := by
    rw [sieve_BS_prodPrimes]
    ext l
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hsq⟩
      exact ⟨⟨hsq.dvd_primorial.trans (primorial_dvd_primorial h2), primorial_ne_zero _⟩, h2⟩
    · rintro ⟨⟨hdvd, -⟩, h2⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hdvd (primorial_pos _), h2⟩, ?_⟩
      exact (squarefree_primorial _).squarefree_of_dvd hdvd
  rw [hset]
  apply sum_congr rfl
  intro l hl
  rw [sieve_selbergTerms_eq s hs _ l (Nat.pos_of_mem_divisors (mem_filter.1 hl).1).ne']

theorem sieve_prod_rho_le_card_divisors (s d : ℕ) (hd : d ≠ 0) :
    ∏ p ∈ d.primeFactors, rho s p ≤ #d.divisors := by
  rw [Nat.card_divisors hd]
  apply prod_le_prod'
  intro p hp
  have : 1 ≤ d.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hd (Nat.dvd_of_mem_primeFactors hp)
  have := sieve_rho_le_two s p
  omega

open Pointwise in
theorem sieve_card_divisors_lcm_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    #(Nat.lcm a b).divisors ≤ #a.divisors * #b.divisors := by
  calc #(Nat.lcm a b).divisors ≤ #(a * b).divisors :=
        card_le_card (Nat.divisors_subset_of_dvd (mul_ne_zero ha hb) (Nat.lcm_dvd_mul a b))
    _ = #(a.divisors * b.divisors) := by rw [Nat.divisors_mul]
    _ ≤ _ := card_mul_le

theorem sieve_sum_card_divisors (N : ℕ) :
    ∑ d ∈ Icc 1 N, (#d.divisors : ℝ) ≤ N * (1 + Real.log N) := by
  have h1 : ∀ d ∈ Icc 1 N, (#d.divisors : ℝ) = ∑ k ∈ Icc 1 N, if k ∣ d then (1 : ℝ) else 0 := by
    intro d hd
    rw [mem_Icc] at hd
    rw [← sum_filter, sum_const, nsmul_one]
    congr 2
    ext k
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hk, -⟩
      have := Nat.le_of_dvd (by omega) hk
      have := Nat.pos_of_dvd_of_pos hk (by omega)
      exact ⟨⟨by omega, by omega⟩, hk⟩
    · rintro ⟨-, hk⟩; exact ⟨hk, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ k ∈ Icc 1 N, (∑ d ∈ Icc 1 N, if k ∣ d then (1 : ℝ) else 0) = ((N / k : ℕ) : ℝ) := by
    intro k _
    rw [← sum_filter, sum_const, nsmul_one, ← Nat.Ioc_filter_dvd_card_eq_div N k]
    congr 3
  rw [sum_congr rfl h2]
  calc ∑ k ∈ Icc 1 N, ((N / k : ℕ) : ℝ) ≤ ∑ k ∈ Icc 1 N, (N : ℝ) * (k : ℝ)⁻¹ := by
        apply sum_le_sum; intro k _
        rw [← div_eq_mul_inv]; exact Nat.cast_div_le
    _ = N * (harmonic N : ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ N * (1 + Real.log N) := by
        gcongr; exact harmonic_le_one_add_log N


/-- Note eq. (7): the Selberg upper-bound sieve with explicit error term,
`S_s(z) ≤ s / G_s(z) + z^2 (1 + log z)^2` for positive even `s` and `z > 1`. -/
theorem sieve_ineq (s : ℕ) (hs : Even s) (hs0 : 0 < s) (z : ℝ) (hz : 1 < z) :
    (S s z : ℝ) ≤ s / G s z + z ^ 2 * (1 + Real.log z) ^ 2 := by
  have hs2 : 2 ∣ s := even_iff_two_dvd.1 hs
  have hN : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hmain := (sieve_BS s hs2 ⌊z⌋₊).siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared _ (sieve_w_one (sieve_BS s hs2 ⌊z⌋₊) ⌊z⌋₊ hN))
  rw [sieve_siftedSum, sieve_BS_totalMass, sieve_mainSum _ _ hN, ← sieve_G_eq] at hmain
  have herr := sieve_errSum_le (sieve_BS s hs2 ⌊z⌋₊) ⌊z⌋₊ hN (fun d => (#d.divisors : ℝ))
    (fun d _ => by positivity)
    (fun d hd => by
      have hdP := Nat.dvd_of_mem_divisors hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      refine (sieve_rem_le s hs2 ⌊z⌋₊ d hdP).trans ?_
      exact_mod_cast sieve_prod_rho_le_card_divisors s d hd0)
    (fun a ha b hb => by
      exact_mod_cast sieve_card_divisors_lcm_le a b (Nat.pos_of_mem_divisors ha).ne'
        (Nat.pos_of_mem_divisors hb).ne')
  have hsum : ∑ d ∈ (sieve_BS s hs2 ⌊z⌋₊).prodPrimes.divisors with d ≤ ⌊z⌋₊, (#d.divisors : ℝ)
      ≤ z * (1 + Real.log z) := by
    calc _ ≤ ∑ d ∈ Icc 1 ⌊z⌋₊, (#d.divisors : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [mem_filter] at hd
            exact mem_Icc.2 ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
          · intro _ _ _; positivity
      _ ≤ ⌊z⌋₊ * (1 + Real.log ⌊z⌋₊) := sieve_sum_card_divisors _
      _ ≤ z * (1 + Real.log z) := by
          have h1 : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hN
          have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
          have h3 : Real.log ⌊z⌋₊ ≤ Real.log z := Real.log_le_log (by linarith) h2
          have h4 : 0 ≤ Real.log ⌊z⌋₊ := Real.log_nonneg h1
          apply mul_le_mul h2 (by linarith) (by linarith) (by linarith)
  have hsum0 : 0 ≤ ∑ d ∈ (sieve_BS s hs2 ⌊z⌋₊).prodPrimes.divisors with d ≤ ⌊z⌋₊,
      (#d.divisors : ℝ) := sum_nonneg fun _ _ => by positivity
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc (S s z : ℝ) ≤ s * (1 / G s z) + _ := hmain
    _ ≤ s * (1 / G s z) + (z * (1 + Real.log z)) ^ 2 := by
        gcongr; exact herr.trans hsq
    _ = s / G s z + z ^ 2 * (1 + Real.log z) ^ 2 := by ring

end Schnir

open Schnir in
theorem solution (s : ℕ) (hs : Even s) (hs0 : 0 < s) (z : ℝ) (hz : 1 < z) :
    (S s z : ℝ) ≤ s / G s z + z ^ 2 * (1 + Real.log z) ^ 2 :=
  Schnir.sieve_ineq s hs hs0 z hz
