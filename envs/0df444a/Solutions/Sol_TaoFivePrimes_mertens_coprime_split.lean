-- Prove2me | solution 1 for TaoFivePrimes.mertens_coprime_split
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:55:50.890606+00:00
-- url     : https://prove2.me/submissions/276e2c4a-13db-4ef6-9740-642301f59654

import Mathlib

open Finset

section PartL46A
open Finset
namespace TaoL46

/-- The weight `mu^2(n)/phi(n)`. -/
noncomputable def wt (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ)

theorem wt_nonneg (n : ℕ) : 0 ≤ wt n := by
  unfold wt; positivity

theorem wt_of_squarefree {n : ℕ} (h : Squarefree n) : wt n = 1 / (Nat.totient n : ℝ) := by
  unfold wt
  have : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 = 1 := by
    have h1 : (ArithmeticFunction.moebius n) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  rw [this]

theorem wt_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) : wt n = 0 := by
  unfold wt
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  simp

/-- The totient of a product of distinct primes. -/
theorem totient_prod_primes :
    ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → Nat.totient (∏ p ∈ t, p) = ∏ p ∈ t, (p - 1) := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert p t hp ih =>
      intro hpr
      have hpprime : p.Prime := hpr p (Finset.mem_insert_self p t)
      have htpr : ∀ r ∈ t, r.Prime := fun r hr => hpr r (Finset.mem_insert_of_mem hr)
      have hcop : Nat.Coprime p (∏ r ∈ t, r) :=
        Nat.Coprime.prod_right (fun r hr =>
          (Nat.coprime_primes hpprime (htpr r hr)).mpr (by rintro rfl; exact hp hr))
      rw [Finset.prod_insert hp, Nat.totient_mul hcop, Nat.totient_prime hpprime,
        Finset.prod_insert hp, ih htpr]

theorem squarefree_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (ht p hp).squarefree)
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (ht a ha) (ht b hb)).mpr hab

theorem wt_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    wt (∏ p ∈ t, p) = ∏ p ∈ t, (1 / ((p : ℝ) - 1)) := by
  have hsq : Squarefree (∏ p ∈ t, p) := squarefree_prod_primes t ht
  rw [wt_of_squarefree hsq, totient_prod_primes t ht, Nat.cast_prod, one_div,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have h1 : 1 ≤ p := (ht p hp).one_lt.le
  rw [one_div]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring

/-- Multiplicativity of the weight on coprime squarefree arguments. -/
theorem wt_mul {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b) :
    wt (a * b) = wt a * wt b := by
  have hsq : Squarefree (a * b) := (Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩)
  rw [wt_of_squarefree hsq, wt_of_squarefree ha, wt_of_squarefree hb,
    Nat.totient_mul hab, Nat.cast_mul]
  field_simp

/-- The primes at most `Q`. -/
def PQ (Q : ℕ) : Finset ℕ := (Finset.Icc 1 Q).filter Nat.Prime

theorem prime_of_mem_PQ {Q p : ℕ} (h : p ∈ PQ Q) : p.Prime := (Finset.mem_filter.mp h).2

theorem mem_PQ_iff {Q p : ℕ} : p ∈ PQ Q ↔ p.Prime ∧ p ≤ Q := by
  simp only [PQ, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1.one_lt.le, h2⟩, h1⟩

/-- The set of small prime factors of `n`. -/
def tp (Q n : ℕ) : Finset ℕ := n.primeFactors ∩ PQ Q

/-- The set of large prime factors of `n`. -/
def sp (Q n : ℕ) : Finset ℕ := n.primeFactors \ PQ Q

/-- The `Q`-smooth part of a squarefree `n`. -/
def dpt (Q n : ℕ) : ℕ := ∏ p ∈ tp Q n, p

/-- The `Q`-rough part of a squarefree `n`. -/
def mpt (Q n : ℕ) : ℕ := ∏ p ∈ sp Q n, p

theorem tp_prime {Q n p : ℕ} (h : p ∈ tp Q n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp h).1

theorem sp_prime {Q n p : ℕ} (h : p ∈ sp Q n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp h).1

theorem tp_subset (Q n : ℕ) : tp Q n ⊆ PQ Q := Finset.inter_subset_right

theorem dpt_mul_mpt {Q n : ℕ} (hn : Squarefree n) : dpt Q n * mpt Q n = n := by
  rw [dpt, mpt, tp, sp, Finset.prod_inter_mul_prod_sdiff]
  exact Nat.prod_primeFactors_of_squarefree hn

theorem mpt_squarefree (Q n : ℕ) : Squarefree (mpt Q n) :=
  squarefree_prod_primes _ (fun p hp => sp_prime hp)

theorem dpt_squarefree (Q n : ℕ) : Squarefree (dpt Q n) :=
  squarefree_prod_primes _ (fun p hp => tp_prime hp)

theorem coprime_dpt_mpt (Q n : ℕ) : Nat.Coprime (dpt Q n) (mpt Q n) := by
  rw [dpt, mpt]
  refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun r hr => ?_))
  refine (Nat.coprime_primes (tp_prime hp) (sp_prime hr)).mpr ?_
  rintro rfl
  exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_inter.mp hp).2

theorem wt_split {Q n : ℕ} (hn : Squarefree n) :
    wt n = (∏ p ∈ tp Q n, (1 / ((p : ℝ) - 1))) * wt (mpt Q n) := by
  conv_lhs => rw [← dpt_mul_mpt (Q := Q) hn]
  rw [wt_mul (dpt_squarefree Q n) (mpt_squarefree Q n) (coprime_dpt_mpt Q n),
    dpt, wt_prod_primes _ (fun p hp => tp_prime hp)]

/-- The `Q`-rough integers up to `R`. -/
def MR (Q R : ℕ) : Finset ℕ := (Finset.Icc 1 R).filter (fun m => ∀ p ∈ PQ Q, ¬ p ∣ m)

theorem mpt_mem_MR {Q R n : ℕ} (hn : Squarefree n) (hnR : n ∈ Finset.Icc 1 R) :
    mpt Q n ∈ MR Q R := by
  rw [Finset.mem_Icc] at hnR
  have hn0 : n ≠ 0 := by omega
  have hdvd : mpt Q n ∣ n :=
    ⟨dpt Q n, by rw [mul_comm]; exact (dpt_mul_mpt (Q := Q) hn).symm⟩
  have hpos : 0 < mpt Q n := Nat.pos_of_ne_zero (by
    intro h; rw [h] at hdvd; exact hn0 (Nat.eq_zero_of_zero_dvd hdvd))
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, ?_⟩, ?_⟩
  · exact le_trans (Nat.le_of_dvd (by omega) hdvd) hnR.2
  · intro p hp hpd
    have hpp : p.Prime := prime_of_mem_PQ hp
    obtain ⟨r, hr, hrd⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hpd
    have : p = r := (Nat.prime_dvd_prime_iff_eq hpp (sp_prime hr)).mp hrd
    exact (Finset.mem_sdiff.mp hr).2 (this ▸ hp)

/-- The Mertens-type splitting: removing the primes up to `Q` from the modulus costs at most
the Euler product `∏_{p ≤ Q} p/(p-1)`. -/
theorem mertens_split (Q R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R, wt n)
      ≤ (∑ m ∈ MR Q R, wt m) * ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 R).filter Squarefree with hS
  set F : ℕ → Finset ℕ × ℕ := fun n => (tp Q n, mpt Q n) with hF
  set g : Finset ℕ × ℕ → ℝ := fun z => (∏ p ∈ z.1, (1 / ((p : ℝ) - 1))) * wt z.2 with hg
  have hgnn : ∀ z ∈ (PQ Q).powerset ×ˢ MR Q R, 0 ≤ g z := by
    intro z hz
    have hz1 : z.1 ⊆ PQ Q := Finset.mem_powerset.mp (Finset.mem_product.mp hz).1
    refine mul_nonneg (Finset.prod_nonneg (fun p hp => ?_)) (wt_nonneg _)
    have hp2 : 2 ≤ p := (prime_of_mem_PQ (hz1 hp)).two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (0:ℝ) < (p:ℝ) - 1 := by linarith
    positivity
  -- step 1: only squarefree numbers contribute
  have hstep1 : (∑ n ∈ Finset.Icc 1 R, wt n) = ∑ n ∈ S, wt n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hns
    exact wt_of_not_squarefree (fun h => hns (Finset.mem_filter.mpr ⟨hn, h⟩))
  -- step 2: reindex by (small primes, rough part)
  have hinj : ∀ n ∈ S, ∀ n' ∈ S, F n = F n' → n = n' := by
    intro n hn n' hn' h
    have h1 : tp Q n = tp Q n' := congrArg Prod.fst h
    have h2 : mpt Q n = mpt Q n' := congrArg Prod.snd h
    have hsq : Squarefree n := (Finset.mem_filter.mp hn).2
    have hsq' : Squarefree n' := (Finset.mem_filter.mp hn').2
    have := dpt_mul_mpt (Q := Q) hsq
    have := dpt_mul_mpt (Q := Q) hsq'
    rw [← dpt_mul_mpt (Q := Q) hsq, ← dpt_mul_mpt (Q := Q) hsq', dpt, dpt, h1, h2]
  have hstep2 : (∑ n ∈ S, wt n) = ∑ z ∈ S.image F, g z := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    exact wt_split (Q := Q) (Finset.mem_filter.mp hn).2
  -- step 3: the image sits inside a product set
  have hsubset : S.image F ⊆ (PQ Q).powerset ×ˢ MR Q R := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (tp_subset Q n), ?_⟩
    exact mpt_mem_MR (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hn).1
  have hstep3 : (∑ z ∈ S.image F, g z) ≤ ∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z hz _ => hgnn z hz)
  -- step 4: factor the product sum
  have hstep4 : (∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z)
      = (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1))) * ∑ m ∈ MR Q R, wt m := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  -- step 5: the Euler product
  have hstep5 : (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1)))
      = ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
    have := Finset.prod_add (fun p : ℕ => (1 / ((p : ℝ) - 1))) (fun _ : ℕ => (1 : ℝ)) (PQ Q)
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := (prime_of_mem_PQ hp).two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hstep1, hstep2]
  calc (∑ z ∈ S.image F, g z)
      ≤ ∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z := hstep3
    _ = (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1))) * ∑ m ∈ MR Q R, wt m := hstep4
    _ = (∑ m ∈ MR Q R, wt m) * ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
        rw [hstep5]; ring

theorem MR_eq (Q R : ℕ) :
    MR Q R
      = (Finset.Icc 1 R).filter
          (fun m => Nat.Coprime m (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, p)) := by
  unfold MR
  refine Finset.filter_congr (fun m _ => ?_)
  constructor
  · intro h
    by_contra hcon
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcon
    have hpm : p ∣ m := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpQ : p ∣ ∏ r ∈ PQ Q, r := hpd.trans (Nat.gcd_dvd_right _ _)
    obtain ⟨r, hr, hrd⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hpQ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp (prime_of_mem_PQ hr)).mp hrd
    exact h p (hpr ▸ hr) hpm
  · intro h p hp hpm
    have hpQ : p ∣ ∏ r ∈ PQ Q, r := Finset.dvd_prod_of_mem _ hp
    have hg : p ∣ Nat.gcd m (∏ r ∈ PQ Q, r) := Nat.dvd_gcd hpm hpQ
    have hh : Nat.gcd m (∏ r ∈ PQ Q, r) = 1 := h
    rw [hh] at hg
    exact Nat.Prime.one_lt (prime_of_mem_PQ hp) |>.ne' (Nat.dvd_one.mp hg)

/-- **Tao, proof of Lemma 4.6**: dropping the primes up to `Q` from the modulus costs at most
the Euler product `∏_{p ≤ Q} p/(p-1)`. -/
theorem mertens_coprime_split (Q R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R,
        ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ))
      ≤ (∑ m ∈ (Finset.Icc 1 R).filter
            (fun m => Nat.Coprime m (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, p)),
          ((ArithmeticFunction.moebius m : ℝ)) ^ 2 / (Nat.totient m : ℝ))
        * ∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h := mertens_split Q R
  rw [MR_eq] at h
  simpa only [wt, PQ] using h

end TaoL46
end PartL46A

theorem solution (Q R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R,
        ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ))
      ≤ (∑ m ∈ (Finset.Icc 1 R).filter
            (fun m => Nat.Coprime m (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, p)),
          ((ArithmeticFunction.moebius m : ℝ)) ^ 2 / (Nat.totient m : ℝ))
        * ∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)) :=
  TaoL46.mertens_coprime_split Q R
