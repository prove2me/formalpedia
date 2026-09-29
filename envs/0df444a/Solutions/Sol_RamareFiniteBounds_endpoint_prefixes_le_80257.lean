-- Prove2me | solution 1 for RamareFiniteBounds.endpoint_prefixes_le_80257
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:12:02.36999+00:00
-- url     : https://prove2.me/submissions/42ca22a9-224b-47a7-8bd9-f0caa1abc361

import Definitions.Def_RamareFiniteBounds
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open RamareFiniteBounds

set_option Elab.async false


set_option autoImplicit false

namespace RamareFiniteBoundsArithmetic

/-- A complete prime-factor list; repeated entries retain multiplicity. -/
private def factorCheck (n : ℕ) (ps : List ℕ) : Bool :=
  decide (ps.prod = n ∧ ∀ p ∈ ps, Nat.Prime p)

private theorem factorCheck_spec (n : ℕ) (ps : List ℕ) :
    factorCheck n ps = true ↔ ps.prod = n ∧ ∀ p ∈ ps, Nat.Prime p := by
  simp only [factorCheck, decide_eq_true_eq]

private theorem prime_list_prod_pos (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p) :
    0 < ps.prod := by
  induction ps with
  | nil => exact Nat.zero_lt_one
  | cons p ps ih =>
    have hhead : Nat.Prime p := hp p (by simp)
    have htail : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (by simp [hq])
    exact Nat.mul_pos hhead.pos (ih htail)

private theorem prime_list_squarefree_iff (ps : List ℕ)
    (hp : ∀ p ∈ ps, Nat.Prime p) : Squarefree ps.prod ↔ ps.Nodup := by
  have hpos := prime_list_prod_pos ps hp
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hp
  exact (Nat.squarefree_iff_nodup_primeFactorsList hpos.ne').trans hperm.nodup_iff.symm

/-- The totient product is needed only for lists without repeated prime factors. -/
private theorem prime_list_totient (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p)
    (hn : ps.Nodup) : Nat.totient ps.prod = (ps.map (fun p => p - 1)).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hhead : Nat.Prime p := hp p (by simp)
    have htail : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (by simp [hq])
    have hnodup : ps.Nodup := (List.nodup_cons.mp hn).2
    have hsq : Squarefree (p * ps.prod) :=
      (prime_list_squarefree_iff (p :: ps) hp).mpr hn
    have hcop : Nat.Coprime p ps.prod := Nat.coprime_of_squarefree_mul hsq
    simp only [List.prod_cons, List.map_cons]
    rw [Nat.totient_mul hcop, Nat.totient_prime hhead, ih htail hnodup]

private theorem factorCheck_pos {n : ℕ} {ps : List ℕ} (h : factorCheck n ps = true) :
    0 < n := by
  rcases (factorCheck_spec n ps).mp h with ⟨hprod, hp⟩
  rw [← hprod]
  exact prime_list_prod_pos ps hp

private theorem factorCheck_squarefree {n : ℕ} {ps : List ℕ}
    (h : factorCheck n ps = true) : Squarefree n ↔ ps.Nodup := by
  rcases (factorCheck_spec n ps).mp h with ⟨hprod, hp⟩
  rw [← hprod]
  exact prime_list_squarefree_iff ps hp

private theorem factorCheck_totient {n : ℕ} {ps : List ℕ}
    (h : factorCheck n ps = true) (hn : ps.Nodup) :
    Nat.totient n = (ps.map (fun p => p - 1)).prod := by
  rcases (factorCheck_spec n ps).mp h with ⟨hprod, hp⟩
  rw [← hprod]
  exact prime_list_totient ps hp hn

/-- Exact rational contribution; duplicate-factor rows do not evaluate a totient. -/
private def factorContribution (ps : List ℕ) : ℚ :=
  if ps.Nodup then (1 : ℚ) / (((ps.map (fun p => p - 1)).prod : ℕ) : ℚ) else 0

private theorem factorContribution_sound {n : ℕ} {ps : List ℕ}
    (h : factorCheck n ps = true) :
    (factorContribution ps : ℝ) =
      (if Squarefree n then (1 : ℝ) / Nat.totient n else 0) := by
  by_cases hn : ps.Nodup
  · have hsf : Squarefree n := (factorCheck_squarefree h).mpr hn
    rw [if_pos hsf, factorCheck_totient h hn]
    simp only [factorContribution, if_pos hn, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  · have hsf : ¬ Squarefree n := fun hs => hn ((factorCheck_squarefree h).mp hs)
    simp only [factorContribution, if_neg hn, if_neg hsf, Rat.cast_zero]

/-- A natural-number row value for fixed-denominator rational upper bounds. -/
private def factorRounded (D : ℕ) (ps : List ℕ) : ℕ :=
  if ps.Nodup then D / (ps.map (fun p => p - 1)).prod + 1 else 0

private theorem factorRounded_sound {n D : ℕ} {ps : List ℕ}
    (h : factorCheck n ps = true) :
    factorRounded D ps = (if Squarefree n then D / Nat.totient n + 1 else 0) := by
  by_cases hn : ps.Nodup
  · have hsf : Squarefree n := (factorCheck_squarefree h).mpr hn
    rw [if_pos hsf, factorCheck_totient h hn]
    simp only [factorRounded, if_pos hn]
  · have hsf : ¬ Squarefree n := fun hs => hn ((factorCheck_squarefree h).mp hs)
    simp only [factorRounded, if_neg hn, if_neg hsf]

end RamareFiniteBoundsArithmetic


set_option autoImplicit false

namespace RamareFiniteBoundsArithmetic

private def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373]

private theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by decide +kernel
private theorem smallPrimes_sorted : smallPrimes.Pairwise (· ≤ ·) := by decide +kernel
private theorem smallPrimes_cover :
    ∀ p ∈ Finset.Icc 2 377, Nat.Prime p → p ∈ smallPrimes := by decide +kernel

/-- Search only a certified, ordered list of possible prime divisors. -/
private def primeTrial (n : ℕ) : List ℕ → ℕ
  | [] => n
  | p :: ps =>
      if n < p * p then n
      else if n % p = 0 then p
      else primeTrial n ps

private theorem prime_of_no_small_prime_divisor (n : ℕ) (hn : 2 ≤ n)
    (hno : ∀ p, Nat.Prime p → p ∣ n → p ≤ Nat.sqrt n → False) : Nat.Prime n := by
  by_contra hnp
  exact hno n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
    (Nat.le_sqrt.mpr (by simpa only [pow_two] using Nat.minFac_sq_le_self (by omega) hnp))

/-- No primality claim depends on an unchecked table: both the prime entries and
coverage of every possible small prime divisor are explicit hypotheses. -/
private theorem primeTrial_sound (n : ℕ) (hn : 2 ≤ n) (ps : List ℕ)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hs : ps.Pairwise (· ≤ ·))
    (hc : ∀ p, Nat.Prime p → p ∣ n → p ≤ Nat.sqrt n → p ∈ ps) :
    Nat.Prime (primeTrial n ps) ∧ primeTrial n ps ∣ n := by
  induction ps with
  | nil =>
    refine ⟨prime_of_no_small_prime_divisor n hn ?_, dvd_refl n⟩
    intro p hprime hdvd hsize
    simpa using hc p hprime hdvd hsize
  | cons p ps ih =>
    have hhead : Nat.Prime p := hp p (by simp)
    have htail : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (by simp [hq])
    have hpair := List.pairwise_cons.mp hs
    by_cases hcut : n < p * p
    · simp only [primeTrial, if_pos hcut]
      refine ⟨prime_of_no_small_prime_divisor n hn ?_, dvd_refl n⟩
      intro q hq hqd hqs
      have hmem := hc q hq hqd hqs
      have hle : p ≤ q := by
        rcases List.mem_cons.mp hmem with he | he
        · exact he.symm.le
        · exact hpair.1 q he
      have hsq : p * p ≤ n :=
        (Nat.mul_le_mul hle hle).trans (Nat.le_sqrt.mp hqs)
      omega
    · by_cases hmod : n % p = 0
      · simp only [primeTrial, if_neg hcut, if_pos hmod]
        exact ⟨hhead, Nat.dvd_of_mod_eq_zero hmod⟩
      · simp only [primeTrial, if_neg hcut, if_neg hmod]
        apply ih htail hpair.2
        intro q hq hqd hqs
        rcases List.mem_cons.mp (hc q hq hqd hqs) with he | he
        · subst q
          exact False.elim (hmod (Nat.mod_eq_zero_of_dvd hqd))
        · exact he

/-- Complete small-prime coverage is kernel-checked once for the fixed bound. -/
private theorem smallPrimeTrial_sound (n : ℕ) (hn : 2 ≤ n) (hb : n ≤ 142300) :
    Nat.Prime (primeTrial n smallPrimes) ∧ primeTrial n smallPrimes ∣ n := by
  apply primeTrial_sound n hn smallPrimes smallPrimes_prime smallPrimes_sorted
  intro p hp hd hs
  apply smallPrimes_cover p _ hp
  refine Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩
  have hsqrt : Nat.sqrt n < 378 := Nat.sqrt_lt.mpr (by omega)
  omega

private def primorial : ℕ := 4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090
private def gcdTrial (n : ℕ) : ℕ :=
  if Nat.gcd n primorial = 1 then n else primeTrial n smallPrimes

private def hybridTrial (n : ℕ) : ℕ :=
  if n % 2 = 0 then 2 else if n % 3 = 0 then 3
  else if n % 5 = 0 then 5 else if n % 7 = 0 then 7
  else gcdTrial n

/-- The literal is the product of the complete, already certified prime table. -/
private theorem primorial_eq_product : primorial = smallPrimes.prod := by
  decide +kernel

/-- A bounded composite has a prime divisor represented in the primorial. -/
private theorem prime_of_primorial_gcd_eq_one (n : ℕ) (hn : 2 ≤ n) (hb : n ≤ 142300)
    (hg : Nat.gcd n primorial = 1) : Nat.Prime n := by
  apply prime_of_no_small_prime_divisor n hn
  intro p hp hpn hps
  have hmem : p ∈ smallPrimes := by
    apply smallPrimes_cover p _ hp
    refine Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩
    have hsqrt : Nat.sqrt n < 378 := Nat.sqrt_lt.mpr (by omega)
    omega
  have hprod : p ∣ primorial := by
    rw [primorial_eq_product]
    exact List.dvd_prod hmem
  have hone : p ∣ 1 := by
    simpa only [hg] using Nat.dvd_gcd hpn hprod
  have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hone
  have htwo := hp.two_le
  omega

/-- The gcd shortcut and the original fallback both return a prime divisor. -/
private theorem gcdTrial_sound (n : ℕ) (hn : 2 ≤ n) (hb : n ≤ 142300) :
    Nat.Prime (gcdTrial n) ∧ gcdTrial n ∣ n := by
  by_cases hg : Nat.gcd n primorial = 1
  · simp only [gcdTrial, if_pos hg]
    exact ⟨prime_of_primorial_gcd_eq_one n hn hb hg, dvd_refl n⟩
  · simpa only [gcdTrial, if_neg hg] using smallPrimeTrial_sound n hn hb

/-- The four presieve branches avoid a gcd on inputs with a very small factor. -/
private theorem hybridTrial_sound (n : ℕ) (hn : 2 ≤ n) (hb : n ≤ 142300) :
    Nat.Prime (hybridTrial n) ∧ hybridTrial n ∣ n := by
  unfold hybridTrial
  split_ifs with h2 h3 h5 h7
  · exact ⟨by decide, Nat.dvd_of_mod_eq_zero h2⟩
  · exact ⟨by decide, Nat.dvd_of_mod_eq_zero h3⟩
  · exact ⟨by decide, Nat.dvd_of_mod_eq_zero h5⟩
  · exact ⟨by decide, Nat.dvd_of_mod_eq_zero h7⟩
  · exact gcdTrial_sound n hn hb


private def primeFactorsFast : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
      if n < 2 then []
      else let p := hybridTrial n
           p :: primeFactorsFast fuel (n / p)

/-- Both output primality and complete product follow by halving the argument. -/
private theorem primeFactorsFast_sound (fuel n : ℕ) (hn : 0 < n) (hb : n ≤ 142300)
    (hf : n < 2 ^ fuel) :
    (primeFactorsFast fuel n).prod = n ∧
      ∀ p ∈ primeFactorsFast fuel n, Nat.Prime p := by
  induction fuel generalizing n with
  | zero => simp only [pow_zero] at hf; omega
  | succ fuel ih =>
    by_cases hsmall : n < 2
    · have he : n = 1 := by omega
      subst n
      simp [primeFactorsFast]
    · have hn2 : 2 ≤ n := by omega
      have hp := hybridTrial_sound n hn2 hb
      let p := hybridTrial n
      have hprime : Nat.Prime p := hp.1
      have hdvd : p ∣ n := hp.2
      have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hdvd) hprime.pos
      have hbound : n / p < 2 ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul hprime.pos).2
        exact lt_of_lt_of_le (by simpa only [pow_succ] using hf)
          (Nat.mul_le_mul_left _ hprime.two_le)
      have hrec := ih (n / p) hquot ((Nat.div_le_self n p).trans hb) hbound
      change (if n < 2 then [] else p :: primeFactorsFast fuel (n / p)).prod = n ∧ _
      simp only [if_neg hsmall, List.prod_cons, hrec.1]
      refine ⟨Nat.mul_div_cancel' hdvd, ?_⟩
      intro q hq
      change q ∈ (if n < 2 then [] else p :: primeFactorsFast fuel (n / p)) at hq
      simp only [if_neg hsmall, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hprime
      · exact hrec.2 q hq

private def boundedPrimeFactors n := primeFactorsFast 18 n

private theorem boundedPrimeFactors_sound (n : ℕ) (hn : 1 ≤ n) (hb : n ≤ 142300) :
    (boundedPrimeFactors n).prod = n ∧
      ∀ p ∈ boundedPrimeFactors n, Nat.Prime p := by
  apply primeFactorsFast_sound 18 n (by omega) hb
  exact lt_of_le_of_lt hb (by decide)

end RamareFiniteBoundsArithmetic


set_option autoImplicit false

namespace RamareFiniteBoundsArithmetic

/-- Consume the factor list structurally, accumulating the totient product.
Duplicate factors return zero before the rest of the list is evaluated. -/
private def scalarRoundedAux (D : ℕ) : List ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => D / acc + 1
  | seen, acc, p :: ps =>
      if p ∈ seen then 0
      else scalarRoundedAux D (p :: seen) (acc * (p - 1)) ps

local instance (ps seen : List ℕ) : Decidable (List.Disjoint ps seen) := by
  unfold List.Disjoint
  infer_instance

/-- The invariant covers arbitrary lists and accumulators, including zero. -/
private theorem scalarRoundedAux_eq (D : ℕ) (ps : List ℕ) :
    ∀ (seen : List ℕ) (acc : ℕ),
      scalarRoundedAux D seen acc ps =
        if ps.Nodup ∧ List.Disjoint ps seen then
          D / (acc * (ps.map (fun p => p - 1)).prod) + 1 else 0 := by
  induction ps with
  | nil =>
    intro seen acc
    simp [scalarRoundedAux]
  | cons p ps ih =>
    intro seen acc
    by_cases h : p ∈ seen
    · simp [scalarRoundedAux, h, List.disjoint_cons_left]
    · simp [scalarRoundedAux, h, ih, List.nodup_cons,
        List.disjoint_cons_left, List.disjoint_cons_right,
        and_assoc, and_left_comm, and_comm, Nat.mul_assoc]

/-- Scalar evaluator with no separate duplicate scan and mapped product. -/
private def scalarRounded (D : ℕ) (ps : List ℕ) : ℕ :=
  scalarRoundedAux D [] 1 ps

private theorem scalarRounded_eq (D : ℕ) (ps : List ℕ) :
    scalarRounded D ps = factorRounded D ps := by
  simpa [scalarRounded, factorRounded] using scalarRoundedAux_eq D ps [] 1

end RamareFiniteBoundsArithmetic

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RamareFiniteBoundsArithmetic



/-- Consume prime factors directly, carrying the scalar evaluator state. -/
private def fusedRounded (D : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ
  | 0, _, _, acc => D / acc + 1
  | fuel + 1, n, seen, acc =>
      if n < 2 then D / acc + 1
      else let p := hybridTrial n
           if p ∈ seen then 0
           else fusedRounded D fuel (n / p) (p :: seen) (acc * (p - 1))

/-- The equality holds for every fuel value, including incomplete factor streams. -/
private theorem fusedRounded_eq (D fuel n : ℕ) (seen : List ℕ) (acc : ℕ) :
    fusedRounded D fuel n seen acc =
      scalarRoundedAux D seen acc (primeFactorsFast fuel n) := by
  induction fuel generalizing n seen acc with
  | zero => rfl
  | succ fuel ih =>
    by_cases hn : n < 2
    · simp only [fusedRounded, primeFactorsFast, if_pos hn, scalarRoundedAux]
    · simp only [fusedRounded, primeFactorsFast, if_neg hn, scalarRoundedAux, ih]

private def boundedFusedRounded (D n : ℕ) : ℕ := fusedRounded D 18 n [] 1

private theorem boundedFusedRounded_eq (D n : ℕ) :
    boundedFusedRounded D n = scalarRounded D (boundedPrimeFactors n) :=
  fusedRounded_eq D 18 n [] 1


/-- Sum an interval without constructing a finite-set or mapped list. -/
private def fastSumAux (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | lo, len + 1, acc => fastSumAux f (lo + 1) len (acc + f lo)

private theorem fastSumAux_eq (f : ℕ → ℕ) (len : ℕ) :
    ∀ lo acc, fastSumAux f lo len acc =
      acc + ∑ i ∈ Finset.range len, f (lo + i) := by
  induction len with
  | zero => intro lo acc; simp [fastSumAux]
  | succ len ih =>
    intro lo acc
    rw [fastSumAux, ih, Finset.sum_range_succ']
    have he : (∑ i ∈ Finset.range len, f (lo + 1 + i)) =
        ∑ i ∈ Finset.range len, f (lo + (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [he]
    simp only [Nat.add_zero]
    omega

private def fastSum (f : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  fastSumAux f lo (hi + 1 - lo) 0

/-- Includes empty and reversed intervals, with natural truncated subtraction. -/
private theorem fastSum_eq (f : ℕ → ℕ) (lo hi : ℕ) :
    fastSum f lo hi = ∑ n ∈ Finset.Icc lo hi, f n := by
  rw [fastSum, fastSumAux_eq, Nat.zero_add,
    ← Finset.sum_Ico_eq_sum_range, Finset.Ico_add_one_right_eq_Icc]


/-- Generic factorization soundness replaces every per-row product replay. -/
private theorem boundedPrimeFactors_check (n : ℕ) (hn : 1 ≤ n) (hb : n ≤ 142300) :
    factorCheck n (boundedPrimeFactors n) = true :=
  (factorCheck_spec n (boundedPrimeFactors n)).mpr (boundedPrimeFactors_sound n hn hb)

/-- The scalar evaluator equals the original arithmetic summand on the full domain. -/
private theorem roundedTerm_eq_scalarRounded (D n : ℕ) (hn : 1 ≤ n) (hb : n ≤ 142300) :
    roundedTerm D n = scalarRounded D (boundedPrimeFactors n) := by
  rw [scalarRounded_eq]
  exact (factorRounded_sound (D := D) (boundedPrimeFactors_check n hn hb)).symm

/-- Transfer an exact inclusive batch to the unchanged totient interface. -/
private theorem semantic_batch_of_prime_factors (D lo hi total : ℕ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 142300)
    (hw : (∑ n ∈ Finset.Icc lo hi, scalarRounded D (boundedPrimeFactors n)) = total) :
    (∑ n ∈ Finset.Icc lo hi, roundedTerm D n) = total := by
  calc
    _ = ∑ n ∈ Finset.Icc lo hi, scalarRounded D (boundedPrimeFactors n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact roundedTerm_eq_scalarRounded D n
        (hlo.trans (Finset.mem_Icc.mp hn).1)
        ((Finset.mem_Icc.mp hn).2.trans hhi)
    _ = total := hw

/-- Transport the fused numerical sum through the generic evaluator equality. -/
private theorem semantic_batch_of_fused_factors (D lo hi total : ℕ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 142300)
    (hw : (∑ n ∈ Finset.Icc lo hi, boundedFusedRounded D n) = total) :
    (∑ n ∈ Finset.Icc lo hi, roundedTerm D n) = total := by
  apply semantic_batch_of_prime_factors D lo hi total hlo hhi
  calc
    _ = ∑ n ∈ Finset.Icc lo hi, boundedFusedRounded D n := by
      apply Finset.sum_congr rfl
      intro n _
      exact (boundedFusedRounded_eq D n).symm
    _ = total := hw

/-- The executable interval sum retains the inclusive public batch endpoints. -/
private theorem semantic_batch_of_fused_fast_sum (D lo hi total : ℕ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 142300)
    (hw : fastSum (boundedFusedRounded D) lo hi = total) :
    (∑ n ∈ Finset.Icc lo hi, roundedTerm D n) = total := by
  apply semantic_batch_of_fused_factors D lo hi total hlo hhi
  exact (fastSum_eq (boundedFusedRounded D) lo hi).symm.trans hw

-- BEGIN CHECKED SQUARE-EXIT EVALUATOR

/-- Exit on a repeated prime before dividing the remaining argument. -/
private def squareExitRounded (trial : ℕ → ℕ) (D : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => D / acc + 1
  | fuel + 1, n, acc =>
      if n < 2 then D / acc + 1
      else let p := trial n
           if n % (p * p) = 0 then 0
           else squareExitRounded trial D fuel (n / p) (acc * (p - 1))

private def boundedSquareExitRounded (trial : ℕ → ℕ) (D n : ℕ) : ℕ :=
  squareExitRounded trial D 18 n 1

/-- A prime occurring only once is coprime to the remaining quotient. -/
private theorem prime_division_coprime {n p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ n)
    (hsq : ¬ p * p ∣ n) : Nat.Coprime p (n / p) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hquot
  apply hsq
  have hmul : p * p ∣ p * (n / p) := Nat.mul_dvd_mul_left p hquot
  simpa only [Nat.mul_div_cancel' hdvd] using hmul

/-- Prime division halves the argument, so a strict power-of-two bound
prevents fuel exhaustion while a nontrivial factor remains. -/
private theorem squareExitRounded_sound (trial : ℕ → ℕ) (limit D fuel n acc : ℕ)
    (htrial : ∀ m, 2 ≤ m → m ≤ limit → Nat.Prime (trial m) ∧ trial m ∣ m)
    (hn : 0 < n) (hlimit : n ≤ limit) (hfuel : n < 2 ^ fuel) :
    squareExitRounded trial D fuel n acc =
      if Squarefree n then D / (acc * n.totient) + 1 else 0 := by
  induction fuel generalizing n acc with
  | zero =>
      simp only [pow_zero] at hfuel
      omega
  | succ fuel ih =>
      by_cases hsmall : n < 2
      · have he : n = 1 := by omega
        subst n
        simp [squareExitRounded]
      · have hn2 : 2 ≤ n := by omega
        let p := trial n
        have hp : Nat.Prime p := (htrial n hn2 hlimit).1
        have hdvd : p ∣ n := (htrial n hn2 hlimit).2
        have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
        rw [squareExitRounded, if_neg hsmall]
        change (if n % (p * p) = 0 then 0 else
          squareExitRounded trial D fuel (n / p) (acc * (p - 1))) = _
        by_cases hmod : n % (p * p) = 0
        · have hns : ¬ Squarefree n := by
            intro hsf
            exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
              (Nat.dvd_of_mod_eq_zero hmod)
          rw [if_pos hmod, if_neg hns]
        · have hsq : ¬ p * p ∣ n := fun h => hmod (Nat.mod_eq_zero_of_dvd h)
          have hcop : Nat.Coprime p (n / p) := prime_division_coprime hp hdvd hsq
          have hqpos : 0 < n / p :=
            Nat.div_pos (Nat.le_of_dvd hn hdvd) hp.pos
          have hqlimit : n / p ≤ limit := (Nat.div_le_self n p).trans hlimit
          have hqfuel : n / p < 2 ^ fuel := by
            apply (Nat.div_lt_iff_lt_mul hp.pos).2
            have hm : 2 ^ fuel * 2 ≤ 2 ^ fuel * p :=
              Nat.mul_le_mul_left _ hp.two_le
            exact lt_of_lt_of_le (by simpa only [pow_succ] using hfuel) hm
          have hsf : Squarefree n ↔ Squarefree (n / p) := by
            calc
              Squarefree n ↔ Squarefree (p * (n / p)) := by rw [hmul]
              _ ↔ Squarefree p ∧ Squarefree (n / p) := Nat.squarefree_mul hcop
              _ ↔ Squarefree (n / p) := and_iff_right hp.squarefree
          have hphi : n.totient = (p - 1) * (n / p).totient := by
            calc
              n.totient = (p * (n / p)).totient := congrArg Nat.totient hmul.symm
              _ = p.totient * (n / p).totient := Nat.totient_mul hcop
              _ = (p - 1) * (n / p).totient := by rw [Nat.totient_prime hp]
          rw [if_neg hmod, ih (n / p) (acc * (p - 1)) hqpos hqlimit hqfuel]
          by_cases hqsf : Squarefree (n / p)
          · rw [if_pos hqsf, if_pos (hsf.mpr hqsf), hphi, Nat.mul_assoc]
          · rw [if_neg hqsf, if_neg (fun h => hqsf (hsf.mp h))]

/-- The original finite target range fits the unchanged allowance of 18 divisions. -/
private theorem boundedSquareExitRounded_sound (trial : ℕ → ℕ) (D n : ℕ)
    (htrial : ∀ m, 2 ≤ m → m ≤ 142300 → Nat.Prime (trial m) ∧ trial m ∣ m)
    (hn : 1 ≤ n) (hupper : n ≤ 142300) :
    boundedSquareExitRounded trial D n =
      if Squarefree n then D / n.totient + 1 else 0 := by
  have hpow : (142300 : ℕ) < 2 ^ 18 := by decide
  have h := squareExitRounded_sound trial 142300 D 18 n 1 htrial
    (by omega) hupper (lt_of_le_of_lt hupper hpow)
  simpa only [boundedSquareExitRounded, one_mul] using h


/-- Specialize the checked prime-selector recursion to the public summand. -/
private theorem roundedTerm_eq_squareExitRounded (D n : ℕ)
    (hn : 1 ≤ n) (hb : n ≤ 142300) :
    roundedTerm D n = boundedSquareExitRounded hybridTrial D n := by
  have h := boundedSquareExitRounded_sound hybridTrial D n hybridTrial_sound hn hb
  simpa only [roundedTerm] using h.symm

/-- Transfer the executable sum directly to the exact public totient sum. -/
private theorem semantic_batch_of_square_exit_fast_sum (D lo hi total : ℕ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 142300)
    (hw : fastSum (boundedSquareExitRounded hybridTrial D) lo hi = total) :
    (∑ n ∈ Finset.Icc lo hi, roundedTerm D n) = total := by
  calc
    _ = ∑ n ∈ Finset.Icc lo hi, boundedSquareExitRounded hybridTrial D n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact roundedTerm_eq_squareExitRounded D n
        (hlo.trans (Finset.mem_Icc.mp hn).1)
        ((Finset.mem_Icc.mp hn).2.trans hhi)
    _ = fastSum (boundedSquareExitRounded hybridTrial D) lo hi :=
      (fastSum_eq (boundedSquareExitRounded hybridTrial D) lo hi).symm
    _ = total := hw

-- END CHECKED SQUARE-EXIT EVALUATOR


end RamareFiniteBoundsArithmetic

namespace RamareFiniteBoundsArithmetic

private structure BatchRow where
  lo : ℕ
  hi : ℕ
  value : ℕ
  deriving DecidableEq

private structure EndpointBatchGroup where
  endpoint : LogEndpoint
  batches : List BatchRow
  deriving DecidableEq

/-- Metadata only: semantic equalities for the batch values are separate. -/
private def batchChainCheck : ℕ → ℕ → ℕ → ℕ → List BatchRow → Bool
  | next, acc, stop, total, [] => decide (next = stop + 1 ∧ acc = total)
  | next, acc, stop, total, b :: bs =>
      decide (b.lo = next ∧ b.lo ≤ b.hi) &&
        batchChainCheck (b.hi + 1) (acc + b.value) stop total bs

private theorem batchChainCheck_sound (f : ℕ → ℕ) (rows : List BatchRow)
    (next acc stop total : ℕ) (hnext : 1 ≤ next)
    (hprefix : (∑ n ∈ Finset.Ico 1 next, f n) = acc)
    (hcheck : batchChainCheck next acc stop total rows = true)
    (hrows : ∀ b ∈ rows, (∑ n ∈ Finset.Icc b.lo b.hi, f n) = b.value) :
    (∑ n ∈ Finset.Icc 1 stop, f n) = total := by
  induction rows generalizing next acc with
  | nil =>
    simp only [batchChainCheck, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨hstop, htotal⟩
    simpa only [hstop, htotal, Finset.Ico_add_one_right_eq_Icc] using hprefix
  | cons b bs ih =>
    simp only [batchChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hlo, hnonempty⟩, htail⟩
    have hbatch : (∑ n ∈ Finset.Ico next (b.hi + 1), f n) = b.value := by
      rw [Finset.Ico_add_one_right_eq_Icc, ← hlo]
      exact hrows b (by simp)
    have hprefix' : (∑ n ∈ Finset.Ico 1 (b.hi + 1), f n) = acc + b.value := by
      calc
        _ = (∑ n ∈ Finset.Ico 1 next, f n) +
            ∑ n ∈ Finset.Ico next (b.hi + 1), f n :=
          (Finset.sum_Ico_consecutive f hnext (by omega)).symm
        _ = acc + b.value := by rw [hprefix, hbatch]
    exact ih (b.hi + 1) (acc + b.value) (by omega) hprefix' htail
      (fun c hc => hrows c (by simp [hc]))

private def batchGroupsCheck : ℕ → ℕ → List EndpointBatchGroup → Bool
  | _, _, [] => true
  | next, acc, g :: gs =>
      batchChainCheck next acc g.endpoint.hi g.endpoint.upper g.batches &&
        batchGroupsCheck (g.endpoint.hi + 1) g.endpoint.upper gs

/-- The semantic input is exactly one equality for every arithmetic batch. -/
private theorem batchGroupsCheck_sound (f : ℕ → ℕ) (groups : List EndpointBatchGroup)
    (next acc : ℕ) (hnext : 1 ≤ next)
    (hprefix : (∑ n ∈ Finset.Ico 1 next, f n) = acc)
    (hcheck : batchGroupsCheck next acc groups = true)
    (hsem : ∀ g ∈ groups, ∀ b ∈ g.batches,
      (∑ n ∈ Finset.Icc b.lo b.hi, f n) = b.value) :
    ∀ g ∈ groups, (∑ n ∈ Finset.Icc 1 g.endpoint.hi, f n) = g.endpoint.upper := by
  induction groups generalizing next acc with
  | nil => simp
  | cons g gs ih =>
    simp only [batchGroupsCheck, Bool.and_eq_true] at hcheck
    rcases hcheck with ⟨hfirst, htail⟩
    have hcurrent : (∑ n ∈ Finset.Icc 1 g.endpoint.hi, f n) = g.endpoint.upper :=
      batchChainCheck_sound f g.batches next acc g.endpoint.hi g.endpoint.upper
        hnext hprefix hfirst (hsem g (by simp))
    have hprefix' : (∑ n ∈ Finset.Ico 1 (g.endpoint.hi + 1), f n) =
        g.endpoint.upper := by
      simpa only [Finset.Ico_add_one_right_eq_Icc] using hcurrent
    have hrest := ih (g.endpoint.hi + 1) g.endpoint.upper (by omega) hprefix' htail
      (fun h hh => hsem h (by simp [hh]))
    intro h hh
    rcases List.mem_cons.mp hh with hsame | hmem
    · subst h
      exact hcurrent
    · exact hrest h hmem

private def batchGroups : List EndpointBatchGroup :=
  [
    ⟨⟨1, 1, 0, 10000000001⟩, [
      ⟨1, 1, 10000000001⟩
    ]⟩,
    ⟨⟨2, 2, 1, 20000000002⟩, [
      ⟨2, 2, 10000000001⟩
    ]⟩,
    ⟨⟨3, 4, 1, 25000000003⟩, [
      ⟨3, 4, 5000000001⟩
    ]⟩,
    ⟨⟨5, 5, 2, 27500000004⟩, [
      ⟨5, 5, 2500000001⟩
    ]⟩,
    ⟨⟨6, 6, 2, 32500000005⟩, [
      ⟨6, 6, 5000000001⟩
    ]⟩,
    ⟨⟨7, 9, 2, 34166666672⟩, [
      ⟨7, 9, 1666666667⟩
    ]⟩,
    ⟨⟨10, 12, 3, 37666666674⟩, [
      ⟨10, 12, 3500000002⟩
    ]⟩,
    ⟨⟨13, 14, 3, 40166666675⟩, [
      ⟨13, 14, 2500000001⟩
    ]⟩,
    ⟨⟨15, 16, 3, 41416666676⟩, [
      ⟨15, 16, 1250000001⟩
    ]⟩,
    ⟨⟨17, 20, 4, 42597222233⟩, [
      ⟨17, 20, 1180555557⟩
    ]⟩,
    ⟨⟨21, 25, 4, 44885101023⟩, [
      ⟨21, 25, 2287878790⟩
    ]⟩,
    ⟨⟨26, 29, 4, 46075577215⟩, [
      ⟨26, 29, 1190476192⟩
    ]⟩,
    ⟨⟨30, 33, 4, 48158910551⟩, [
      ⟨30, 33, 2083333336⟩
    ]⟩,
    ⟨⟨34, 37, 5, 49478354997⟩, [
      ⟨34, 37, 1319444446⟩
    ]⟩,
    ⟨⟨38, 41, 5, 50700577221⟩, [
      ⟨38, 41, 1222222224⟩
    ]⟩,
    ⟨⟨42, 45, 5, 51772005794⟩, [
      ⟨42, 45, 1071428573⟩
    ]⟩,
    ⟨⟨46, 54, 5, 52948750248⟩, [
      ⟨46, 54, 1176744454⟩
    ]⟩,
    ⟨⟨55, 65, 5, 54714418014⟩, [
      ⟨55, 65, 1765667766⟩
    ]⟩,
    ⟨⟨66, 76, 6, 56569396372⟩, [
      ⟨66, 76, 1854978358⟩
    ]⟩,
    ⟨⟨77, 86, 6, 58047231296⟩, [
      ⟨77, 86, 1477834924⟩
    ]⟩,
    ⟨⟨87, 101, 6, 59205441507⟩, [
      ⟨87, 101, 1158210211⟩
    ]⟩,
    ⟨⟨102, 113, 6, 60681728572⟩, [
      ⟨102, 113, 1476287065⟩
    ]⟩,
    ⟨⟨114, 130, 6, 62048135877⟩, [
      ⟨114, 130, 1366407305⟩
    ]⟩,
    ⟨⟨131, 153, 7, 63439727577⟩, [
      ⟨131, 153, 1391591700⟩
    ]⟩,
    ⟨⟨154, 180, 7, 65071851278⟩, [
      ⟨154, 180, 1632123701⟩
    ]⟩,
    ⟨⟨181, 209, 7, 66653078926⟩, [
      ⟨181, 209, 1581227648⟩
    ]⟩,
    ⟨⟨210, 237, 7, 68123849868⟩, [
      ⟨210, 237, 1470770942⟩
    ]⟩,
    ⟨⟨238, 272, 7, 69378252149⟩, [
      ⟨238, 272, 1254402281⟩
    ]⟩,
    ⟨⟨273, 313, 8, 70755760372⟩, [
      ⟨273, 313, 1377508223⟩
    ]⟩,
    ⟨⟨314, 365, 8, 72195842919⟩, [
      ⟨314, 365, 1440082547⟩
    ]⟩,
    ⟨⟨366, 421, 8, 73706126532⟩, [
      ⟨366, 421, 1510283613⟩
    ]⟩,
    ⟨⟨422, 481, 8, 75144228761⟩, [
      ⟨422, 481, 1438102229⟩
    ]⟩,
    ⟨⟨482, 553, 8, 76484834138⟩, [
      ⟨482, 553, 1340605377⟩
    ]⟩,
    ⟨⟨554, 634, 9, 77878820124⟩, [
      ⟨554, 634, 1393985986⟩
    ]⟩,
    ⟨⟨635, 729, 9, 79243799040⟩, [
      ⟨635, 729, 1364978916⟩
    ]⟩,
    ⟨⟨730, 834, 9, 80631110893⟩, [
      ⟨730, 834, 1387311853⟩
    ]⟩,
    ⟨⟨835, 958, 9, 81978547871⟩, [
      ⟨835, 958, 1347436978⟩
    ]⟩,
    ⟨⟨959, 1105, 9, 83348286055⟩, [
      ⟨959, 1105, 1369738184⟩
    ]⟩,
    ⟨⟨1106, 1269, 10, 84784450761⟩, [
      ⟨1106, 1269, 1436164706⟩
    ]⟩,
    ⟨⟨1270, 1453, 10, 86168594696⟩, [
      ⟨1270, 1453, 1384143935⟩
    ]⟩,
    ⟨⟨1454, 1661, 10, 87522766859⟩, [
      ⟨1454, 1661, 1354172163⟩
    ]⟩,
    ⟨⟨1662, 1913, 10, 88860271373⟩, [
      ⟨1662, 1913, 1337504514⟩
    ]⟩,
    ⟨⟨1914, 2201, 10, 90269228769⟩, [
      ⟨1914, 2169, 1257441540⟩,
      ⟨2170, 2201, 151515856⟩
    ]⟩,
    ⟨⟨2202, 2525, 11, 91678279488⟩, [
      ⟨2202, 2457, 1125692620⟩,
      ⟨2458, 2525, 283358099⟩
    ]⟩,
    ⟨⟨2526, 2905, 11, 93048242808⟩, [
      ⟨2526, 2781, 956690076⟩,
      ⟨2782, 2905, 413273244⟩
    ]⟩,
    ⟨⟨2906, 3332, 11, 94449403959⟩, [
      ⟨2906, 3161, 875810957⟩,
      ⟨3162, 3332, 525350194⟩
    ]⟩,
    ⟨⟨3333, 3829, 11, 95820608345⟩, [
      ⟨3333, 3588, 742196810⟩,
      ⟨3589, 3829, 629007576⟩
    ]⟩,
    ⟨⟨3830, 4396, 11, 97213969920⟩, [
      ⟨3830, 4085, 658796753⟩,
      ⟨4086, 4341, 610319354⟩,
      ⟨4342, 4396, 124245468⟩
    ]⟩,
    ⟨⟨4397, 5038, 12, 98593944130⟩, [
      ⟨4397, 4652, 563425174⟩,
      ⟨4653, 4908, 548817745⟩,
      ⟨4909, 5038, 267731291⟩
    ]⟩,
    ⟨⟨5039, 5797, 12, 99957414198⟩, [
      ⟨5039, 5294, 467629489⟩,
      ⟨5295, 5550, 471209651⟩,
      ⟨5551, 5797, 424630928⟩
    ]⟩,
    ⟨⟨5798, 6660, 12, 101360837942⟩, [
      ⟨5798, 6053, 439861773⟩,
      ⟨6054, 6309, 427335251⟩,
      ⟨6310, 6565, 397844359⟩,
      ⟨6566, 6660, 138382361⟩
    ]⟩,
    ⟨⟨6661, 7646, 12, 102749074130⟩, [
      ⟨6661, 6916, 382518035⟩,
      ⟨6917, 7172, 357291322⟩,
      ⟨7173, 7428, 356264568⟩,
      ⟨7429, 7646, 292162263⟩
    ]⟩,
    ⟨⟨7647, 8777, 12, 104125057472⟩, [
      ⟨7647, 7902, 335207460⟩,
      ⟨7903, 8158, 313925294⟩,
      ⟨8159, 8414, 308387560⟩,
      ⟨8415, 8670, 298580584⟩,
      ⟨8671, 8777, 119882444⟩
    ]⟩,
    ⟨⟨8778, 10073, 13, 105506430410⟩, [
      ⟨8778, 9033, 291234201⟩,
      ⟨9034, 9289, 283681873⟩,
      ⟨9290, 9545, 270892333⟩,
      ⟨9546, 9801, 266965918⟩,
      ⟨9802, 10057, 252556888⟩,
      ⟨10058, 10073, 16041725⟩
    ]⟩,
    ⟨⟨10074, 11569, 13, 106885038573⟩, [
      ⟨10074, 10329, 249560863⟩,
      ⟨10330, 10585, 244724495⟩,
      ⟨10586, 10841, 238348793⟩,
      ⟨10842, 11097, 228758713⟩,
      ⟨11098, 11353, 224317872⟩,
      ⟨11354, 11569, 192897427⟩
    ]⟩,
    ⟨⟨11570, 13288, 13, 108270576051⟩, [
      ⟨11570, 11825, 218431610⟩,
      ⟨11826, 12081, 210378837⟩,
      ⟨12082, 12337, 213929423⟩,
      ⟨12338, 12593, 200813739⟩,
      ⟨12594, 12849, 201822570⟩,
      ⟨12850, 13105, 200917719⟩,
      ⟨13106, 13288, 139243580⟩
    ]⟩,
    ⟨⟨13289, 15262, 13, 109655338876⟩, [
      ⟨13289, 13544, 190398955⟩,
      ⟨13545, 13800, 181261818⟩,
      ⟨13801, 14056, 183697555⟩,
      ⟨14057, 14312, 181782860⟩,
      ⟨14313, 14568, 176065524⟩,
      ⟨14569, 14824, 175648990⟩,
      ⟨14825, 15080, 176792584⟩,
      ⟨15081, 15262, 119114539⟩
    ]⟩,
    ⟨⟨15263, 17521, 13, 111040440149⟩, [
      ⟨15263, 15518, 170684343⟩,
      ⟨15519, 15774, 165259543⟩,
      ⟨15775, 16030, 157513993⟩,
      ⟨16031, 16286, 156532696⟩,
      ⟨16287, 16542, 159015920⟩,
      ⟨16543, 16798, 154401272⟩,
      ⟨16799, 17054, 149457196⟩,
      ⟨17055, 17310, 150219824⟩,
      ⟨17311, 17521, 122016486⟩
    ]⟩,
    ⟨⟨17522, 20118, 14, 112420936661⟩, [
      ⟨17522, 17777, 144263293⟩,
      ⟨17778, 18033, 142303562⟩,
      ⟨18034, 18289, 143006219⟩,
      ⟨18290, 18545, 141192750⟩,
      ⟨18546, 18801, 133837167⟩,
      ⟨18802, 19057, 137537739⟩,
      ⟨19058, 19313, 128572988⟩,
      ⟨19314, 19569, 131926984⟩,
      ⟨19570, 19825, 133013354⟩,
      ⟨19826, 20081, 127518583⟩,
      ⟨20082, 20118, 17323873⟩
    ]⟩,
    ⟨⟨20119, 23105, 14, 113802112086⟩, [
      ⟨20119, 20374, 128703431⟩,
      ⟨20375, 20630, 122396740⟩,
      ⟨20631, 20886, 122927183⟩,
      ⟨20887, 21142, 121569082⟩,
      ⟨21143, 21398, 122793765⟩,
      ⟨21399, 21654, 118541049⟩,
      ⟨21655, 21910, 116778831⟩,
      ⟨21911, 22166, 116527713⟩,
      ⟨22167, 22422, 113092159⟩,
      ⟨22423, 22678, 109408931⟩,
      ⟨22679, 22934, 114009546⟩,
      ⟨22935, 23105, 74426995⟩
    ]⟩,
    ⟨⟨23106, 26534, 14, 115187036893⟩, [
      ⟨23106, 23361, 111181278⟩,
      ⟨23362, 23617, 109358531⟩,
      ⟨23618, 23873, 107336910⟩,
      ⟨23874, 24129, 108228645⟩,
      ⟨24130, 24385, 104473840⟩,
      ⟨24386, 24641, 104741206⟩,
      ⟨24642, 24897, 102799527⟩,
      ⟨24898, 25153, 101539229⟩,
      ⟨25154, 25409, 98585211⟩,
      ⟨25410, 25665, 102034021⟩,
      ⟨25666, 25921, 101201271⟩,
      ⟨25922, 26177, 96701389⟩,
      ⟨26178, 26433, 97835010⟩,
      ⟨26434, 26534, 38908739⟩
    ]⟩,
    ⟨⟨26535, 30465, 14, 116570808110⟩, [
      ⟨26535, 26790, 96767627⟩,
      ⟨26791, 27046, 94284698⟩,
      ⟨27047, 27302, 95195270⟩,
      ⟨27303, 27558, 94253201⟩,
      ⟨27559, 27814, 94496551⟩,
      ⟨27815, 28070, 88312146⟩,
      ⟨28071, 28326, 90179516⟩,
      ⟨28327, 28582, 91684795⟩,
      ⟨28583, 28838, 87642441⟩,
      ⟨28839, 29094, 90398140⟩,
      ⟨29095, 29350, 88014046⟩,
      ⟨29351, 29606, 87295616⟩,
      ⟨29607, 29862, 84598220⟩,
      ⟨29863, 30118, 85904555⟩,
      ⟨30119, 30374, 83322766⟩,
      ⟨30375, 30465, 31421629⟩
    ]⟩,
    ⟨⟨30466, 34989, 14, 117952577160⟩, [
      ⟨30466, 30721, 83443044⟩,
      ⟨30722, 30977, 81674244⟩,
      ⟨30978, 31233, 81906926⟩,
      ⟨31234, 31489, 79979107⟩,
      ⟨31490, 31745, 81511538⟩,
      ⟨31746, 32001, 80275914⟩,
      ⟨32002, 32257, 78606007⟩,
      ⟨32258, 32513, 79933012⟩,
      ⟨32514, 32769, 79504176⟩,
      ⟨32770, 33025, 76681151⟩,
      ⟨33026, 33281, 76362242⟩,
      ⟨33282, 33537, 78616172⟩,
      ⟨33538, 33793, 76875894⟩,
      ⟨33794, 34049, 76216916⟩,
      ⟨34050, 34305, 73723652⟩,
      ⟨34306, 34561, 73602092⟩,
      ⟨34562, 34817, 74186458⟩,
      ⟨34818, 34989, 48670505⟩
    ]⟩,
    ⟨⟨34990, 40190, 15, 119336869463⟩, [
      ⟨34990, 35245, 73216499⟩,
      ⟨35246, 35501, 70029195⟩,
      ⟨35502, 35757, 72302290⟩,
      ⟨35758, 36013, 73143217⟩,
      ⟨36014, 36269, 71343939⟩,
      ⟨36270, 36525, 70123751⟩,
      ⟨36526, 36781, 70779459⟩,
      ⟨36782, 37037, 67511995⟩,
      ⟨37038, 37293, 69133610⟩,
      ⟨37294, 37549, 66602734⟩,
      ⟨37550, 37805, 67819251⟩,
      ⟨37806, 38061, 69053028⟩,
      ⟨38062, 38317, 68018157⟩,
      ⟨38318, 38573, 66333748⟩,
      ⟨38574, 38829, 63843221⟩,
      ⟨38830, 39085, 64589544⟩,
      ⟨39086, 39341, 66638019⟩,
      ⟨39342, 39597, 64431036⟩,
      ⟨39598, 39853, 64599569⟩,
      ⟨39854, 40109, 63590007⟩,
      ⟨40110, 40190, 21190034⟩
    ]⟩,
    ⟨⟨40191, 46144, 15, 120722814528⟩, [
      ⟨40191, 40446, 62965214⟩,
      ⟨40447, 40702, 63410299⟩,
      ⟨40703, 40958, 62617042⟩,
      ⟨40959, 41214, 62682730⟩,
      ⟨41215, 41470, 61255500⟩,
      ⟨41471, 41726, 62616196⟩,
      ⟨41727, 41982, 62269740⟩,
      ⟨41983, 42238, 59976859⟩,
      ⟨42239, 42494, 61087295⟩,
      ⟨42495, 42750, 61107721⟩,
      ⟨42751, 43006, 60218071⟩,
      ⟨43007, 43262, 59672803⟩,
      ⟨43263, 43518, 59342670⟩,
      ⟨43519, 43774, 58706992⟩,
      ⟨43775, 44030, 58614023⟩,
      ⟨44031, 44286, 56748687⟩,
      ⟨44287, 44542, 57727724⟩,
      ⟨44543, 44798, 57803673⟩,
      ⟨44799, 45054, 56385097⟩,
      ⟨45055, 45310, 57010852⟩,
      ⟨45311, 45566, 58027300⟩,
      ⟨45567, 45822, 55633192⟩,
      ⟨45823, 46078, 55778081⟩,
      ⟨46079, 46144, 14287304⟩
    ]⟩,
    ⟨⟨46145, 52976, 15, 122104241703⟩, [
      ⟨46145, 46400, 55398756⟩,
      ⟨46401, 46656, 55697240⟩,
      ⟨46657, 46912, 56336150⟩,
      ⟨46913, 47168, 54056855⟩,
      ⟨47169, 47424, 54993569⟩,
      ⟨47425, 47680, 52514899⟩,
      ⟨47681, 47936, 53479331⟩,
      ⟨47937, 48192, 52610236⟩,
      ⟨48193, 48448, 52694840⟩,
      ⟨48449, 48704, 52529069⟩,
      ⟨48705, 48960, 52345146⟩,
      ⟨48961, 49216, 52184386⟩,
      ⟨49217, 49472, 52034752⟩,
      ⟨49473, 49728, 50759454⟩,
      ⟨49729, 49984, 51812320⟩,
      ⟨49985, 50240, 52207458⟩,
      ⟨50241, 50496, 48961788⟩,
      ⟨50497, 50752, 51191196⟩,
      ⟨50753, 51008, 51177519⟩,
      ⟨51009, 51264, 49001997⟩,
      ⟨51265, 51520, 50932507⟩,
      ⟨51521, 51776, 50072294⟩,
      ⟨51777, 52032, 49835077⟩,
      ⟨52033, 52288, 47884001⟩,
      ⟨52289, 52544, 48729438⟩,
      ⟨52545, 52800, 48929459⟩,
      ⟨52801, 52976, 33057438⟩
    ]⟩,
    ⟨⟨52977, 60832, 15, 123485008269⟩, [
      ⟨52977, 53232, 47515943⟩,
      ⟨53233, 53488, 47385780⟩,
      ⟨53489, 53744, 48789929⟩,
      ⟨53745, 54000, 46775237⟩,
      ⟨54001, 54256, 47970488⟩,
      ⟨54257, 54512, 48066858⟩,
      ⟨54513, 54768, 47202653⟩,
      ⟨54769, 55024, 46042637⟩,
      ⟨55025, 55280, 46261098⟩,
      ⟨55281, 55536, 45716142⟩,
      ⟨55537, 55792, 44133985⟩,
      ⟨55793, 56048, 46198331⟩,
      ⟨56049, 56304, 45760728⟩,
      ⟨56305, 56560, 44532061⟩,
      ⟨56561, 56816, 45513458⟩,
      ⟨56817, 57072, 45009904⟩,
      ⟨57073, 57328, 44608001⟩,
      ⟨57329, 57584, 43461989⟩,
      ⟨57585, 57840, 45707674⟩,
      ⟨57841, 58096, 44034700⟩,
      ⟨58097, 58352, 43591524⟩,
      ⟨58353, 58608, 43587599⟩,
      ⟨58609, 58864, 43540012⟩,
      ⟨58865, 59120, 44398095⟩,
      ⟨59121, 59376, 42937333⟩,
      ⟨59377, 59632, 43869039⟩,
      ⟨59633, 59888, 41201000⟩,
      ⟨59889, 60144, 43841351⟩,
      ⟨60145, 60400, 41208121⟩,
      ⟨60401, 60656, 43145648⟩,
      ⟨60657, 60832, 28759248⟩
    ]⟩,
    ⟨⟨60833, 69861, 15, 124867807525⟩, [
      ⟨60833, 61088, 42304125⟩,
      ⟨61089, 61344, 42443978⟩,
      ⟨61345, 61600, 41430460⟩,
      ⟨61601, 61856, 40659192⟩,
      ⟨61857, 62112, 41990843⟩,
      ⟨62113, 62368, 41359918⟩,
      ⟨62369, 62624, 40883419⟩,
      ⟨62625, 62880, 39433339⟩,
      ⟨62881, 63136, 40948357⟩,
      ⟨63137, 63392, 40306543⟩,
      ⟨63393, 63648, 41049866⟩,
      ⟨63649, 63904, 39362074⟩,
      ⟨63905, 64160, 39649859⟩,
      ⟨64161, 64416, 40665015⟩,
      ⟨64417, 64672, 38997169⟩,
      ⟨64673, 64928, 39881411⟩,
      ⟨64929, 65184, 38841177⟩,
      ⟨65185, 65440, 39851876⟩,
      ⟨65441, 65696, 38351304⟩,
      ⟨65697, 65952, 38404310⟩,
      ⟨65953, 66208, 38889418⟩,
      ⟨66209, 66464, 38727906⟩,
      ⟨66465, 66720, 38574413⟩,
      ⟨66721, 66976, 37908451⟩,
      ⟨66977, 67232, 38030454⟩,
      ⟨67233, 67488, 37713340⟩,
      ⟨67489, 67744, 38441569⟩,
      ⟨67745, 68000, 38534151⟩,
      ⟨68001, 68256, 37733330⟩,
      ⟨68257, 68512, 37120072⟩,
      ⟨68513, 68768, 37080671⟩,
      ⟨68769, 69024, 35992201⟩,
      ⟨69025, 69280, 37133549⟩,
      ⟨69281, 69536, 36134437⟩,
      ⟨69537, 69792, 38414517⟩,
      ⟨69793, 69861, 9556542⟩
    ]⟩,
    ⟨⟨69862, 80257, 16, 126251687858⟩, [
      ⟨69862, 70117, 36835716⟩,
      ⟨70118, 70373, 35939257⟩,
      ⟨70374, 70629, 35831719⟩,
      ⟨70630, 70885, 36544640⟩,
      ⟨70886, 71141, 36269793⟩,
      ⟨71142, 71397, 35124141⟩,
      ⟨71398, 71653, 36610432⟩,
      ⟨71654, 71909, 36934002⟩,
      ⟨71910, 72165, 34632516⟩,
      ⟨72166, 72421, 35802355⟩,
      ⟨72422, 72677, 34483080⟩,
      ⟨72678, 72933, 35939899⟩,
      ⟨72934, 73189, 33804211⟩,
      ⟨73190, 73445, 35047788⟩,
      ⟨73446, 73701, 34951410⟩,
      ⟨73702, 73957, 34139579⟩,
      ⟨73958, 74213, 34846601⟩,
      ⟨74214, 74469, 33972736⟩,
      ⟨74470, 74725, 34139810⟩,
      ⟨74726, 74981, 33590839⟩,
      ⟨74982, 75237, 34940670⟩,
      ⟨75238, 75493, 34190570⟩,
      ⟨75494, 75749, 33527821⟩,
      ⟨75750, 76005, 33271456⟩,
      ⟨76006, 76261, 34223745⟩,
      ⟨76262, 76517, 34836821⟩,
      ⟨76518, 76773, 31701456⟩,
      ⟨76774, 77029, 33543245⟩,
      ⟨77030, 77285, 33138513⟩,
      ⟨77286, 77541, 33148204⟩,
      ⟨77542, 77797, 32308150⟩,
      ⟨77798, 78053, 33195150⟩,
      ⟨78054, 78309, 32223214⟩,
      ⟨78310, 78565, 33459542⟩,
      ⟨78566, 78821, 32575459⟩,
      ⟨78822, 79077, 31763807⟩,
      ⟨79078, 79333, 31323817⟩,
      ⟨79334, 79589, 32326351⟩,
      ⟨79590, 79845, 32880226⟩,
      ⟨79846, 80101, 31444808⟩,
      ⟨80102, 80257, 18416784⟩
    ]⟩
  ]

/-- Exact filtered public endpoints; all four record fields are preserved. -/
private theorem batchGroups_endpoints :
    batchGroups.map EndpointBatchGroup.endpoint =
      logEndpoints.filter (fun e => decide (e.hi ≤ 80257)) := by
  decide +kernel

/-- Contiguous interval and integer-total checks only. -/
private theorem batchGroups_checked : batchGroupsCheck 1 0 batchGroups = true := by
  decide +kernel

private theorem weights000 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1 1 = 10000000001 := by
  decide +kernel

private theorem batch000 :
    (∑ n ∈ Finset.Icc 1 1, roundedTerm 10000000000 n) = 10000000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1 1 10000000001
    (by decide) (by decide) weights000

private theorem weights001 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2 2 = 10000000001 := by
  decide +kernel

private theorem batch001 :
    (∑ n ∈ Finset.Icc 2 2, roundedTerm 10000000000 n) = 10000000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2 2 10000000001
    (by decide) (by decide) weights001

private theorem weights002 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 3 4 = 5000000001 := by
  decide +kernel

private theorem batch002 :
    (∑ n ∈ Finset.Icc 3 4, roundedTerm 10000000000 n) = 5000000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 3 4 5000000001
    (by decide) (by decide) weights002

private theorem weights003 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 5 5 = 2500000001 := by
  decide +kernel

private theorem batch003 :
    (∑ n ∈ Finset.Icc 5 5, roundedTerm 10000000000 n) = 2500000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 5 5 2500000001
    (by decide) (by decide) weights003

private theorem weights004 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6 6 = 5000000001 := by
  decide +kernel

private theorem batch004 :
    (∑ n ∈ Finset.Icc 6 6, roundedTerm 10000000000 n) = 5000000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6 6 5000000001
    (by decide) (by decide) weights004

private theorem weights005 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 7 9 = 1666666667 := by
  decide +kernel

private theorem batch005 :
    (∑ n ∈ Finset.Icc 7 9, roundedTerm 10000000000 n) = 1666666667 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 7 9 1666666667
    (by decide) (by decide) weights005

private theorem weights006 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10 12 = 3500000002 := by
  decide +kernel

private theorem batch006 :
    (∑ n ∈ Finset.Icc 10 12, roundedTerm 10000000000 n) = 3500000002 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10 12 3500000002
    (by decide) (by decide) weights006

private theorem weights007 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 13 14 = 2500000001 := by
  decide +kernel

private theorem batch007 :
    (∑ n ∈ Finset.Icc 13 14, roundedTerm 10000000000 n) = 2500000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 13 14 2500000001
    (by decide) (by decide) weights007

private theorem weights008 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 15 16 = 1250000001 := by
  decide +kernel

private theorem batch008 :
    (∑ n ∈ Finset.Icc 15 16, roundedTerm 10000000000 n) = 1250000001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 15 16 1250000001
    (by decide) (by decide) weights008

private theorem weights009 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 17 20 = 1180555557 := by
  decide +kernel

private theorem batch009 :
    (∑ n ∈ Finset.Icc 17 20, roundedTerm 10000000000 n) = 1180555557 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 17 20 1180555557
    (by decide) (by decide) weights009

private theorem weights010 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 21 25 = 2287878790 := by
  decide +kernel

private theorem batch010 :
    (∑ n ∈ Finset.Icc 21 25, roundedTerm 10000000000 n) = 2287878790 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 21 25 2287878790
    (by decide) (by decide) weights010

private theorem weights011 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 26 29 = 1190476192 := by
  decide +kernel

private theorem batch011 :
    (∑ n ∈ Finset.Icc 26 29, roundedTerm 10000000000 n) = 1190476192 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 26 29 1190476192
    (by decide) (by decide) weights011

private theorem weights012 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30 33 = 2083333336 := by
  decide +kernel

private theorem batch012 :
    (∑ n ∈ Finset.Icc 30 33, roundedTerm 10000000000 n) = 2083333336 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30 33 2083333336
    (by decide) (by decide) weights012

private theorem weights013 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34 37 = 1319444446 := by
  decide +kernel

private theorem batch013 :
    (∑ n ∈ Finset.Icc 34 37, roundedTerm 10000000000 n) = 1319444446 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34 37 1319444446
    (by decide) (by decide) weights013

private theorem weights014 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 38 41 = 1222222224 := by
  decide +kernel

private theorem batch014 :
    (∑ n ∈ Finset.Icc 38 41, roundedTerm 10000000000 n) = 1222222224 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 38 41 1222222224
    (by decide) (by decide) weights014

private theorem weights015 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 42 45 = 1071428573 := by
  decide +kernel

private theorem batch015 :
    (∑ n ∈ Finset.Icc 42 45, roundedTerm 10000000000 n) = 1071428573 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 42 45 1071428573
    (by decide) (by decide) weights015

private theorem weights016 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46 54 = 1176744454 := by
  decide +kernel

private theorem batch016 :
    (∑ n ∈ Finset.Icc 46 54, roundedTerm 10000000000 n) = 1176744454 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46 54 1176744454
    (by decide) (by decide) weights016

private theorem weights017 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 55 65 = 1765667766 := by
  decide +kernel

private theorem batch017 :
    (∑ n ∈ Finset.Icc 55 65, roundedTerm 10000000000 n) = 1765667766 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 55 65 1765667766
    (by decide) (by decide) weights017

private theorem weights018 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 66 76 = 1854978358 := by
  decide +kernel

private theorem batch018 :
    (∑ n ∈ Finset.Icc 66 76, roundedTerm 10000000000 n) = 1854978358 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 66 76 1854978358
    (by decide) (by decide) weights018

private theorem weights019 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 77 86 = 1477834924 := by
  decide +kernel

private theorem batch019 :
    (∑ n ∈ Finset.Icc 77 86, roundedTerm 10000000000 n) = 1477834924 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 77 86 1477834924
    (by decide) (by decide) weights019

private theorem weights020 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 87 101 = 1158210211 := by
  decide +kernel

private theorem batch020 :
    (∑ n ∈ Finset.Icc 87 101, roundedTerm 10000000000 n) = 1158210211 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 87 101 1158210211
    (by decide) (by decide) weights020

private theorem weights021 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 102 113 = 1476287065 := by
  decide +kernel

private theorem batch021 :
    (∑ n ∈ Finset.Icc 102 113, roundedTerm 10000000000 n) = 1476287065 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 102 113 1476287065
    (by decide) (by decide) weights021

private theorem weights022 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 114 130 = 1366407305 := by
  decide +kernel

private theorem batch022 :
    (∑ n ∈ Finset.Icc 114 130, roundedTerm 10000000000 n) = 1366407305 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 114 130 1366407305
    (by decide) (by decide) weights022

private theorem weights023 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 131 153 = 1391591700 := by
  decide +kernel

private theorem batch023 :
    (∑ n ∈ Finset.Icc 131 153, roundedTerm 10000000000 n) = 1391591700 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 131 153 1391591700
    (by decide) (by decide) weights023

private theorem weights024 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 154 180 = 1632123701 := by
  decide +kernel

private theorem batch024 :
    (∑ n ∈ Finset.Icc 154 180, roundedTerm 10000000000 n) = 1632123701 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 154 180 1632123701
    (by decide) (by decide) weights024

private theorem weights025 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 181 209 = 1581227648 := by
  decide +kernel

private theorem batch025 :
    (∑ n ∈ Finset.Icc 181 209, roundedTerm 10000000000 n) = 1581227648 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 181 209 1581227648
    (by decide) (by decide) weights025

private theorem weights026 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 210 237 = 1470770942 := by
  decide +kernel

private theorem batch026 :
    (∑ n ∈ Finset.Icc 210 237, roundedTerm 10000000000 n) = 1470770942 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 210 237 1470770942
    (by decide) (by decide) weights026

private theorem weights027 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 238 272 = 1254402281 := by
  decide +kernel

private theorem batch027 :
    (∑ n ∈ Finset.Icc 238 272, roundedTerm 10000000000 n) = 1254402281 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 238 272 1254402281
    (by decide) (by decide) weights027

private theorem weights028 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 273 313 = 1377508223 := by
  decide +kernel

private theorem batch028 :
    (∑ n ∈ Finset.Icc 273 313, roundedTerm 10000000000 n) = 1377508223 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 273 313 1377508223
    (by decide) (by decide) weights028

private theorem weights029 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 314 365 = 1440082547 := by
  decide +kernel

private theorem batch029 :
    (∑ n ∈ Finset.Icc 314 365, roundedTerm 10000000000 n) = 1440082547 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 314 365 1440082547
    (by decide) (by decide) weights029

private theorem weights030 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 366 421 = 1510283613 := by
  decide +kernel

private theorem batch030 :
    (∑ n ∈ Finset.Icc 366 421, roundedTerm 10000000000 n) = 1510283613 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 366 421 1510283613
    (by decide) (by decide) weights030

private theorem weights031 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 422 481 = 1438102229 := by
  decide +kernel

private theorem batch031 :
    (∑ n ∈ Finset.Icc 422 481, roundedTerm 10000000000 n) = 1438102229 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 422 481 1438102229
    (by decide) (by decide) weights031

set_option trace.profiler true in
private theorem weights032 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 482 553 = 1340605377 := by
  decide +kernel

private theorem batch032 :
    (∑ n ∈ Finset.Icc 482 553, roundedTerm 10000000000 n) = 1340605377 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 482 553 1340605377
    (by decide) (by decide) weights032

private theorem weights033 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 554 634 = 1393985986 := by
  decide +kernel

private theorem batch033 :
    (∑ n ∈ Finset.Icc 554 634, roundedTerm 10000000000 n) = 1393985986 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 554 634 1393985986
    (by decide) (by decide) weights033

private theorem weights034 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 635 729 = 1364978916 := by
  decide +kernel

private theorem batch034 :
    (∑ n ∈ Finset.Icc 635 729, roundedTerm 10000000000 n) = 1364978916 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 635 729 1364978916
    (by decide) (by decide) weights034

private theorem weights035 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 730 834 = 1387311853 := by
  decide +kernel

private theorem batch035 :
    (∑ n ∈ Finset.Icc 730 834, roundedTerm 10000000000 n) = 1387311853 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 730 834 1387311853
    (by decide) (by decide) weights035

private theorem weights036 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 835 958 = 1347436978 := by
  decide +kernel

private theorem batch036 :
    (∑ n ∈ Finset.Icc 835 958, roundedTerm 10000000000 n) = 1347436978 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 835 958 1347436978
    (by decide) (by decide) weights036

private theorem weights037 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 959 1105 = 1369738184 := by
  decide +kernel

private theorem batch037 :
    (∑ n ∈ Finset.Icc 959 1105, roundedTerm 10000000000 n) = 1369738184 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 959 1105 1369738184
    (by decide) (by decide) weights037

private theorem weights038 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1106 1269 = 1436164706 := by
  decide +kernel

private theorem batch038 :
    (∑ n ∈ Finset.Icc 1106 1269, roundedTerm 10000000000 n) = 1436164706 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1106 1269 1436164706
    (by decide) (by decide) weights038

private theorem weights039 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1270 1453 = 1384143935 := by
  decide +kernel

private theorem batch039 :
    (∑ n ∈ Finset.Icc 1270 1453, roundedTerm 10000000000 n) = 1384143935 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1270 1453 1384143935
    (by decide) (by decide) weights039

private theorem weights040 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1454 1661 = 1354172163 := by
  decide +kernel

private theorem batch040 :
    (∑ n ∈ Finset.Icc 1454 1661, roundedTerm 10000000000 n) = 1354172163 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1454 1661 1354172163
    (by decide) (by decide) weights040

private theorem weights041 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1662 1913 = 1337504514 := by
  decide +kernel

private theorem batch041 :
    (∑ n ∈ Finset.Icc 1662 1913, roundedTerm 10000000000 n) = 1337504514 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1662 1913 1337504514
    (by decide) (by decide) weights041

private theorem weights042 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 1914 2169 = 1257441540 := by
  decide +kernel

private theorem batch042 :
    (∑ n ∈ Finset.Icc 1914 2169, roundedTerm 10000000000 n) = 1257441540 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 1914 2169 1257441540
    (by decide) (by decide) weights042

private theorem weights043 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2170 2201 = 151515856 := by
  decide +kernel

private theorem batch043 :
    (∑ n ∈ Finset.Icc 2170 2201, roundedTerm 10000000000 n) = 151515856 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2170 2201 151515856
    (by decide) (by decide) weights043

private theorem weights044 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2202 2457 = 1125692620 := by
  decide +kernel

private theorem batch044 :
    (∑ n ∈ Finset.Icc 2202 2457, roundedTerm 10000000000 n) = 1125692620 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2202 2457 1125692620
    (by decide) (by decide) weights044

private theorem weights045 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2458 2525 = 283358099 := by
  decide +kernel

private theorem batch045 :
    (∑ n ∈ Finset.Icc 2458 2525, roundedTerm 10000000000 n) = 283358099 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2458 2525 283358099
    (by decide) (by decide) weights045

private theorem weights046 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2526 2781 = 956690076 := by
  decide +kernel

private theorem batch046 :
    (∑ n ∈ Finset.Icc 2526 2781, roundedTerm 10000000000 n) = 956690076 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2526 2781 956690076
    (by decide) (by decide) weights046

private theorem weights047 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2782 2905 = 413273244 := by
  decide +kernel

private theorem batch047 :
    (∑ n ∈ Finset.Icc 2782 2905, roundedTerm 10000000000 n) = 413273244 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2782 2905 413273244
    (by decide) (by decide) weights047

private theorem weights048 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 2906 3161 = 875810957 := by
  decide +kernel

private theorem batch048 :
    (∑ n ∈ Finset.Icc 2906 3161, roundedTerm 10000000000 n) = 875810957 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 2906 3161 875810957
    (by decide) (by decide) weights048

private theorem weights049 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 3162 3332 = 525350194 := by
  decide +kernel

private theorem batch049 :
    (∑ n ∈ Finset.Icc 3162 3332, roundedTerm 10000000000 n) = 525350194 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 3162 3332 525350194
    (by decide) (by decide) weights049

private theorem weights050 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 3333 3588 = 742196810 := by
  decide +kernel

private theorem batch050 :
    (∑ n ∈ Finset.Icc 3333 3588, roundedTerm 10000000000 n) = 742196810 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 3333 3588 742196810
    (by decide) (by decide) weights050

private theorem weights051 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 3589 3829 = 629007576 := by
  decide +kernel

private theorem batch051 :
    (∑ n ∈ Finset.Icc 3589 3829, roundedTerm 10000000000 n) = 629007576 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 3589 3829 629007576
    (by decide) (by decide) weights051

private theorem weights052 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 3830 4085 = 658796753 := by
  decide +kernel

private theorem batch052 :
    (∑ n ∈ Finset.Icc 3830 4085, roundedTerm 10000000000 n) = 658796753 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 3830 4085 658796753
    (by decide) (by decide) weights052

private theorem weights053 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 4086 4341 = 610319354 := by
  decide +kernel

private theorem batch053 :
    (∑ n ∈ Finset.Icc 4086 4341, roundedTerm 10000000000 n) = 610319354 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 4086 4341 610319354
    (by decide) (by decide) weights053

private theorem weights054 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 4342 4396 = 124245468 := by
  decide +kernel

private theorem batch054 :
    (∑ n ∈ Finset.Icc 4342 4396, roundedTerm 10000000000 n) = 124245468 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 4342 4396 124245468
    (by decide) (by decide) weights054

private theorem weights055 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 4397 4652 = 563425174 := by
  decide +kernel

private theorem batch055 :
    (∑ n ∈ Finset.Icc 4397 4652, roundedTerm 10000000000 n) = 563425174 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 4397 4652 563425174
    (by decide) (by decide) weights055

private theorem weights056 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 4653 4908 = 548817745 := by
  decide +kernel

private theorem batch056 :
    (∑ n ∈ Finset.Icc 4653 4908, roundedTerm 10000000000 n) = 548817745 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 4653 4908 548817745
    (by decide) (by decide) weights056

private theorem weights057 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 4909 5038 = 267731291 := by
  decide +kernel

private theorem batch057 :
    (∑ n ∈ Finset.Icc 4909 5038, roundedTerm 10000000000 n) = 267731291 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 4909 5038 267731291
    (by decide) (by decide) weights057

private theorem weights058 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 5039 5294 = 467629489 := by
  decide +kernel

private theorem batch058 :
    (∑ n ∈ Finset.Icc 5039 5294, roundedTerm 10000000000 n) = 467629489 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 5039 5294 467629489
    (by decide) (by decide) weights058

private theorem weights059 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 5295 5550 = 471209651 := by
  decide +kernel

private theorem batch059 :
    (∑ n ∈ Finset.Icc 5295 5550, roundedTerm 10000000000 n) = 471209651 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 5295 5550 471209651
    (by decide) (by decide) weights059

private theorem weights060 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 5551 5797 = 424630928 := by
  decide +kernel

private theorem batch060 :
    (∑ n ∈ Finset.Icc 5551 5797, roundedTerm 10000000000 n) = 424630928 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 5551 5797 424630928
    (by decide) (by decide) weights060

private theorem weights061 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 5798 6053 = 439861773 := by
  decide +kernel

private theorem batch061 :
    (∑ n ∈ Finset.Icc 5798 6053, roundedTerm 10000000000 n) = 439861773 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 5798 6053 439861773
    (by decide) (by decide) weights061

private theorem weights062 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6054 6309 = 427335251 := by
  decide +kernel

private theorem batch062 :
    (∑ n ∈ Finset.Icc 6054 6309, roundedTerm 10000000000 n) = 427335251 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6054 6309 427335251
    (by decide) (by decide) weights062

private theorem weights063 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6310 6565 = 397844359 := by
  decide +kernel

private theorem batch063 :
    (∑ n ∈ Finset.Icc 6310 6565, roundedTerm 10000000000 n) = 397844359 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6310 6565 397844359
    (by decide) (by decide) weights063

set_option trace.profiler true in
private theorem weights064 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6566 6660 = 138382361 := by
  decide +kernel

private theorem batch064 :
    (∑ n ∈ Finset.Icc 6566 6660, roundedTerm 10000000000 n) = 138382361 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6566 6660 138382361
    (by decide) (by decide) weights064

private theorem weights065 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6661 6916 = 382518035 := by
  decide +kernel

private theorem batch065 :
    (∑ n ∈ Finset.Icc 6661 6916, roundedTerm 10000000000 n) = 382518035 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6661 6916 382518035
    (by decide) (by decide) weights065

private theorem weights066 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 6917 7172 = 357291322 := by
  decide +kernel

private theorem batch066 :
    (∑ n ∈ Finset.Icc 6917 7172, roundedTerm 10000000000 n) = 357291322 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 6917 7172 357291322
    (by decide) (by decide) weights066

private theorem weights067 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 7173 7428 = 356264568 := by
  decide +kernel

private theorem batch067 :
    (∑ n ∈ Finset.Icc 7173 7428, roundedTerm 10000000000 n) = 356264568 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 7173 7428 356264568
    (by decide) (by decide) weights067

private theorem weights068 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 7429 7646 = 292162263 := by
  decide +kernel

private theorem batch068 :
    (∑ n ∈ Finset.Icc 7429 7646, roundedTerm 10000000000 n) = 292162263 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 7429 7646 292162263
    (by decide) (by decide) weights068

private theorem weights069 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 7647 7902 = 335207460 := by
  decide +kernel

private theorem batch069 :
    (∑ n ∈ Finset.Icc 7647 7902, roundedTerm 10000000000 n) = 335207460 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 7647 7902 335207460
    (by decide) (by decide) weights069

private theorem weights070 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 7903 8158 = 313925294 := by
  decide +kernel

private theorem batch070 :
    (∑ n ∈ Finset.Icc 7903 8158, roundedTerm 10000000000 n) = 313925294 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 7903 8158 313925294
    (by decide) (by decide) weights070

private theorem weights071 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 8159 8414 = 308387560 := by
  decide +kernel

private theorem batch071 :
    (∑ n ∈ Finset.Icc 8159 8414, roundedTerm 10000000000 n) = 308387560 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 8159 8414 308387560
    (by decide) (by decide) weights071

private theorem weights072 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 8415 8670 = 298580584 := by
  decide +kernel

private theorem batch072 :
    (∑ n ∈ Finset.Icc 8415 8670, roundedTerm 10000000000 n) = 298580584 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 8415 8670 298580584
    (by decide) (by decide) weights072

private theorem weights073 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 8671 8777 = 119882444 := by
  decide +kernel

private theorem batch073 :
    (∑ n ∈ Finset.Icc 8671 8777, roundedTerm 10000000000 n) = 119882444 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 8671 8777 119882444
    (by decide) (by decide) weights073

private theorem weights074 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 8778 9033 = 291234201 := by
  decide +kernel

private theorem batch074 :
    (∑ n ∈ Finset.Icc 8778 9033, roundedTerm 10000000000 n) = 291234201 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 8778 9033 291234201
    (by decide) (by decide) weights074

private theorem weights075 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 9034 9289 = 283681873 := by
  decide +kernel

private theorem batch075 :
    (∑ n ∈ Finset.Icc 9034 9289, roundedTerm 10000000000 n) = 283681873 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 9034 9289 283681873
    (by decide) (by decide) weights075

private theorem weights076 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 9290 9545 = 270892333 := by
  decide +kernel

private theorem batch076 :
    (∑ n ∈ Finset.Icc 9290 9545, roundedTerm 10000000000 n) = 270892333 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 9290 9545 270892333
    (by decide) (by decide) weights076

private theorem weights077 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 9546 9801 = 266965918 := by
  decide +kernel

private theorem batch077 :
    (∑ n ∈ Finset.Icc 9546 9801, roundedTerm 10000000000 n) = 266965918 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 9546 9801 266965918
    (by decide) (by decide) weights077

private theorem weights078 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 9802 10057 = 252556888 := by
  decide +kernel

private theorem batch078 :
    (∑ n ∈ Finset.Icc 9802 10057, roundedTerm 10000000000 n) = 252556888 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 9802 10057 252556888
    (by decide) (by decide) weights078

private theorem weights079 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10058 10073 = 16041725 := by
  decide +kernel

private theorem batch079 :
    (∑ n ∈ Finset.Icc 10058 10073, roundedTerm 10000000000 n) = 16041725 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10058 10073 16041725
    (by decide) (by decide) weights079

private theorem weights080 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10074 10329 = 249560863 := by
  decide +kernel

private theorem batch080 :
    (∑ n ∈ Finset.Icc 10074 10329, roundedTerm 10000000000 n) = 249560863 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10074 10329 249560863
    (by decide) (by decide) weights080

private theorem weights081 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10330 10585 = 244724495 := by
  decide +kernel

private theorem batch081 :
    (∑ n ∈ Finset.Icc 10330 10585, roundedTerm 10000000000 n) = 244724495 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10330 10585 244724495
    (by decide) (by decide) weights081

private theorem weights082 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10586 10841 = 238348793 := by
  decide +kernel

private theorem batch082 :
    (∑ n ∈ Finset.Icc 10586 10841, roundedTerm 10000000000 n) = 238348793 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10586 10841 238348793
    (by decide) (by decide) weights082

private theorem weights083 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 10842 11097 = 228758713 := by
  decide +kernel

private theorem batch083 :
    (∑ n ∈ Finset.Icc 10842 11097, roundedTerm 10000000000 n) = 228758713 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 10842 11097 228758713
    (by decide) (by decide) weights083

private theorem weights084 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 11098 11353 = 224317872 := by
  decide +kernel

private theorem batch084 :
    (∑ n ∈ Finset.Icc 11098 11353, roundedTerm 10000000000 n) = 224317872 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 11098 11353 224317872
    (by decide) (by decide) weights084

private theorem weights085 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 11354 11569 = 192897427 := by
  decide +kernel

private theorem batch085 :
    (∑ n ∈ Finset.Icc 11354 11569, roundedTerm 10000000000 n) = 192897427 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 11354 11569 192897427
    (by decide) (by decide) weights085

private theorem weights086 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 11570 11825 = 218431610 := by
  decide +kernel

private theorem batch086 :
    (∑ n ∈ Finset.Icc 11570 11825, roundedTerm 10000000000 n) = 218431610 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 11570 11825 218431610
    (by decide) (by decide) weights086

private theorem weights087 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 11826 12081 = 210378837 := by
  decide +kernel

private theorem batch087 :
    (∑ n ∈ Finset.Icc 11826 12081, roundedTerm 10000000000 n) = 210378837 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 11826 12081 210378837
    (by decide) (by decide) weights087

private theorem weights088 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 12082 12337 = 213929423 := by
  decide +kernel

private theorem batch088 :
    (∑ n ∈ Finset.Icc 12082 12337, roundedTerm 10000000000 n) = 213929423 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 12082 12337 213929423
    (by decide) (by decide) weights088

private theorem weights089 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 12338 12593 = 200813739 := by
  decide +kernel

private theorem batch089 :
    (∑ n ∈ Finset.Icc 12338 12593, roundedTerm 10000000000 n) = 200813739 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 12338 12593 200813739
    (by decide) (by decide) weights089

private theorem weights090 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 12594 12849 = 201822570 := by
  decide +kernel

private theorem batch090 :
    (∑ n ∈ Finset.Icc 12594 12849, roundedTerm 10000000000 n) = 201822570 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 12594 12849 201822570
    (by decide) (by decide) weights090

private theorem weights091 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 12850 13105 = 200917719 := by
  decide +kernel

private theorem batch091 :
    (∑ n ∈ Finset.Icc 12850 13105, roundedTerm 10000000000 n) = 200917719 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 12850 13105 200917719
    (by decide) (by decide) weights091

private theorem weights092 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 13106 13288 = 139243580 := by
  decide +kernel

private theorem batch092 :
    (∑ n ∈ Finset.Icc 13106 13288, roundedTerm 10000000000 n) = 139243580 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 13106 13288 139243580
    (by decide) (by decide) weights092

private theorem weights093 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 13289 13544 = 190398955 := by
  decide +kernel

private theorem batch093 :
    (∑ n ∈ Finset.Icc 13289 13544, roundedTerm 10000000000 n) = 190398955 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 13289 13544 190398955
    (by decide) (by decide) weights093

private theorem weights094 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 13545 13800 = 181261818 := by
  decide +kernel

private theorem batch094 :
    (∑ n ∈ Finset.Icc 13545 13800, roundedTerm 10000000000 n) = 181261818 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 13545 13800 181261818
    (by decide) (by decide) weights094

private theorem weights095 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 13801 14056 = 183697555 := by
  decide +kernel

private theorem batch095 :
    (∑ n ∈ Finset.Icc 13801 14056, roundedTerm 10000000000 n) = 183697555 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 13801 14056 183697555
    (by decide) (by decide) weights095

set_option trace.profiler true in
private theorem weights096 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 14057 14312 = 181782860 := by
  decide +kernel

private theorem batch096 :
    (∑ n ∈ Finset.Icc 14057 14312, roundedTerm 10000000000 n) = 181782860 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 14057 14312 181782860
    (by decide) (by decide) weights096

private theorem weights097 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 14313 14568 = 176065524 := by
  decide +kernel

private theorem batch097 :
    (∑ n ∈ Finset.Icc 14313 14568, roundedTerm 10000000000 n) = 176065524 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 14313 14568 176065524
    (by decide) (by decide) weights097

private theorem weights098 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 14569 14824 = 175648990 := by
  decide +kernel

private theorem batch098 :
    (∑ n ∈ Finset.Icc 14569 14824, roundedTerm 10000000000 n) = 175648990 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 14569 14824 175648990
    (by decide) (by decide) weights098

private theorem weights099 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 14825 15080 = 176792584 := by
  decide +kernel

private theorem batch099 :
    (∑ n ∈ Finset.Icc 14825 15080, roundedTerm 10000000000 n) = 176792584 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 14825 15080 176792584
    (by decide) (by decide) weights099

private theorem weights100 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 15081 15262 = 119114539 := by
  decide +kernel

private theorem batch100 :
    (∑ n ∈ Finset.Icc 15081 15262, roundedTerm 10000000000 n) = 119114539 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 15081 15262 119114539
    (by decide) (by decide) weights100

private theorem weights101 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 15263 15518 = 170684343 := by
  decide +kernel

private theorem batch101 :
    (∑ n ∈ Finset.Icc 15263 15518, roundedTerm 10000000000 n) = 170684343 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 15263 15518 170684343
    (by decide) (by decide) weights101

private theorem weights102 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 15519 15774 = 165259543 := by
  decide +kernel

private theorem batch102 :
    (∑ n ∈ Finset.Icc 15519 15774, roundedTerm 10000000000 n) = 165259543 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 15519 15774 165259543
    (by decide) (by decide) weights102

private theorem weights103 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 15775 16030 = 157513993 := by
  decide +kernel

private theorem batch103 :
    (∑ n ∈ Finset.Icc 15775 16030, roundedTerm 10000000000 n) = 157513993 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 15775 16030 157513993
    (by decide) (by decide) weights103

private theorem weights104 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 16031 16286 = 156532696 := by
  decide +kernel

private theorem batch104 :
    (∑ n ∈ Finset.Icc 16031 16286, roundedTerm 10000000000 n) = 156532696 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 16031 16286 156532696
    (by decide) (by decide) weights104

private theorem weights105 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 16287 16542 = 159015920 := by
  decide +kernel

private theorem batch105 :
    (∑ n ∈ Finset.Icc 16287 16542, roundedTerm 10000000000 n) = 159015920 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 16287 16542 159015920
    (by decide) (by decide) weights105

private theorem weights106 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 16543 16798 = 154401272 := by
  decide +kernel

private theorem batch106 :
    (∑ n ∈ Finset.Icc 16543 16798, roundedTerm 10000000000 n) = 154401272 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 16543 16798 154401272
    (by decide) (by decide) weights106

private theorem weights107 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 16799 17054 = 149457196 := by
  decide +kernel

private theorem batch107 :
    (∑ n ∈ Finset.Icc 16799 17054, roundedTerm 10000000000 n) = 149457196 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 16799 17054 149457196
    (by decide) (by decide) weights107

private theorem weights108 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 17055 17310 = 150219824 := by
  decide +kernel

private theorem batch108 :
    (∑ n ∈ Finset.Icc 17055 17310, roundedTerm 10000000000 n) = 150219824 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 17055 17310 150219824
    (by decide) (by decide) weights108

private theorem weights109 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 17311 17521 = 122016486 := by
  decide +kernel

private theorem batch109 :
    (∑ n ∈ Finset.Icc 17311 17521, roundedTerm 10000000000 n) = 122016486 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 17311 17521 122016486
    (by decide) (by decide) weights109

private theorem weights110 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 17522 17777 = 144263293 := by
  decide +kernel

private theorem batch110 :
    (∑ n ∈ Finset.Icc 17522 17777, roundedTerm 10000000000 n) = 144263293 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 17522 17777 144263293
    (by decide) (by decide) weights110

private theorem weights111 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 17778 18033 = 142303562 := by
  decide +kernel

private theorem batch111 :
    (∑ n ∈ Finset.Icc 17778 18033, roundedTerm 10000000000 n) = 142303562 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 17778 18033 142303562
    (by decide) (by decide) weights111

private theorem weights112 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 18034 18289 = 143006219 := by
  decide +kernel

private theorem batch112 :
    (∑ n ∈ Finset.Icc 18034 18289, roundedTerm 10000000000 n) = 143006219 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 18034 18289 143006219
    (by decide) (by decide) weights112

private theorem weights113 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 18290 18545 = 141192750 := by
  decide +kernel

private theorem batch113 :
    (∑ n ∈ Finset.Icc 18290 18545, roundedTerm 10000000000 n) = 141192750 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 18290 18545 141192750
    (by decide) (by decide) weights113

private theorem weights114 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 18546 18801 = 133837167 := by
  decide +kernel

private theorem batch114 :
    (∑ n ∈ Finset.Icc 18546 18801, roundedTerm 10000000000 n) = 133837167 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 18546 18801 133837167
    (by decide) (by decide) weights114

private theorem weights115 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 18802 19057 = 137537739 := by
  decide +kernel

private theorem batch115 :
    (∑ n ∈ Finset.Icc 18802 19057, roundedTerm 10000000000 n) = 137537739 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 18802 19057 137537739
    (by decide) (by decide) weights115

private theorem weights116 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 19058 19313 = 128572988 := by
  decide +kernel

private theorem batch116 :
    (∑ n ∈ Finset.Icc 19058 19313, roundedTerm 10000000000 n) = 128572988 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 19058 19313 128572988
    (by decide) (by decide) weights116

private theorem weights117 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 19314 19569 = 131926984 := by
  decide +kernel

private theorem batch117 :
    (∑ n ∈ Finset.Icc 19314 19569, roundedTerm 10000000000 n) = 131926984 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 19314 19569 131926984
    (by decide) (by decide) weights117

private theorem weights118 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 19570 19825 = 133013354 := by
  decide +kernel

private theorem batch118 :
    (∑ n ∈ Finset.Icc 19570 19825, roundedTerm 10000000000 n) = 133013354 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 19570 19825 133013354
    (by decide) (by decide) weights118

private theorem weights119 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 19826 20081 = 127518583 := by
  decide +kernel

private theorem batch119 :
    (∑ n ∈ Finset.Icc 19826 20081, roundedTerm 10000000000 n) = 127518583 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 19826 20081 127518583
    (by decide) (by decide) weights119

private theorem weights120 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 20082 20118 = 17323873 := by
  decide +kernel

private theorem batch120 :
    (∑ n ∈ Finset.Icc 20082 20118, roundedTerm 10000000000 n) = 17323873 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 20082 20118 17323873
    (by decide) (by decide) weights120

private theorem weights121 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 20119 20374 = 128703431 := by
  decide +kernel

private theorem batch121 :
    (∑ n ∈ Finset.Icc 20119 20374, roundedTerm 10000000000 n) = 128703431 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 20119 20374 128703431
    (by decide) (by decide) weights121

private theorem weights122 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 20375 20630 = 122396740 := by
  decide +kernel

private theorem batch122 :
    (∑ n ∈ Finset.Icc 20375 20630, roundedTerm 10000000000 n) = 122396740 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 20375 20630 122396740
    (by decide) (by decide) weights122

private theorem weights123 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 20631 20886 = 122927183 := by
  decide +kernel

private theorem batch123 :
    (∑ n ∈ Finset.Icc 20631 20886, roundedTerm 10000000000 n) = 122927183 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 20631 20886 122927183
    (by decide) (by decide) weights123

private theorem weights124 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 20887 21142 = 121569082 := by
  decide +kernel

private theorem batch124 :
    (∑ n ∈ Finset.Icc 20887 21142, roundedTerm 10000000000 n) = 121569082 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 20887 21142 121569082
    (by decide) (by decide) weights124

private theorem weights125 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 21143 21398 = 122793765 := by
  decide +kernel

private theorem batch125 :
    (∑ n ∈ Finset.Icc 21143 21398, roundedTerm 10000000000 n) = 122793765 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 21143 21398 122793765
    (by decide) (by decide) weights125

private theorem weights126 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 21399 21654 = 118541049 := by
  decide +kernel

private theorem batch126 :
    (∑ n ∈ Finset.Icc 21399 21654, roundedTerm 10000000000 n) = 118541049 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 21399 21654 118541049
    (by decide) (by decide) weights126

private theorem weights127 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 21655 21910 = 116778831 := by
  decide +kernel

private theorem batch127 :
    (∑ n ∈ Finset.Icc 21655 21910, roundedTerm 10000000000 n) = 116778831 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 21655 21910 116778831
    (by decide) (by decide) weights127

set_option trace.profiler true in
private theorem weights128 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 21911 22166 = 116527713 := by
  decide +kernel

private theorem batch128 :
    (∑ n ∈ Finset.Icc 21911 22166, roundedTerm 10000000000 n) = 116527713 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 21911 22166 116527713
    (by decide) (by decide) weights128

private theorem weights129 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 22167 22422 = 113092159 := by
  decide +kernel

private theorem batch129 :
    (∑ n ∈ Finset.Icc 22167 22422, roundedTerm 10000000000 n) = 113092159 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 22167 22422 113092159
    (by decide) (by decide) weights129

private theorem weights130 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 22423 22678 = 109408931 := by
  decide +kernel

private theorem batch130 :
    (∑ n ∈ Finset.Icc 22423 22678, roundedTerm 10000000000 n) = 109408931 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 22423 22678 109408931
    (by decide) (by decide) weights130

private theorem weights131 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 22679 22934 = 114009546 := by
  decide +kernel

private theorem batch131 :
    (∑ n ∈ Finset.Icc 22679 22934, roundedTerm 10000000000 n) = 114009546 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 22679 22934 114009546
    (by decide) (by decide) weights131

private theorem weights132 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 22935 23105 = 74426995 := by
  decide +kernel

private theorem batch132 :
    (∑ n ∈ Finset.Icc 22935 23105, roundedTerm 10000000000 n) = 74426995 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 22935 23105 74426995
    (by decide) (by decide) weights132

private theorem weights133 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 23106 23361 = 111181278 := by
  decide +kernel

private theorem batch133 :
    (∑ n ∈ Finset.Icc 23106 23361, roundedTerm 10000000000 n) = 111181278 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 23106 23361 111181278
    (by decide) (by decide) weights133

private theorem weights134 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 23362 23617 = 109358531 := by
  decide +kernel

private theorem batch134 :
    (∑ n ∈ Finset.Icc 23362 23617, roundedTerm 10000000000 n) = 109358531 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 23362 23617 109358531
    (by decide) (by decide) weights134

private theorem weights135 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 23618 23873 = 107336910 := by
  decide +kernel

private theorem batch135 :
    (∑ n ∈ Finset.Icc 23618 23873, roundedTerm 10000000000 n) = 107336910 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 23618 23873 107336910
    (by decide) (by decide) weights135

private theorem weights136 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 23874 24129 = 108228645 := by
  decide +kernel

private theorem batch136 :
    (∑ n ∈ Finset.Icc 23874 24129, roundedTerm 10000000000 n) = 108228645 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 23874 24129 108228645
    (by decide) (by decide) weights136

private theorem weights137 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 24130 24385 = 104473840 := by
  decide +kernel

private theorem batch137 :
    (∑ n ∈ Finset.Icc 24130 24385, roundedTerm 10000000000 n) = 104473840 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 24130 24385 104473840
    (by decide) (by decide) weights137

private theorem weights138 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 24386 24641 = 104741206 := by
  decide +kernel

private theorem batch138 :
    (∑ n ∈ Finset.Icc 24386 24641, roundedTerm 10000000000 n) = 104741206 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 24386 24641 104741206
    (by decide) (by decide) weights138

private theorem weights139 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 24642 24897 = 102799527 := by
  decide +kernel

private theorem batch139 :
    (∑ n ∈ Finset.Icc 24642 24897, roundedTerm 10000000000 n) = 102799527 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 24642 24897 102799527
    (by decide) (by decide) weights139

private theorem weights140 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 24898 25153 = 101539229 := by
  decide +kernel

private theorem batch140 :
    (∑ n ∈ Finset.Icc 24898 25153, roundedTerm 10000000000 n) = 101539229 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 24898 25153 101539229
    (by decide) (by decide) weights140

private theorem weights141 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 25154 25409 = 98585211 := by
  decide +kernel

private theorem batch141 :
    (∑ n ∈ Finset.Icc 25154 25409, roundedTerm 10000000000 n) = 98585211 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 25154 25409 98585211
    (by decide) (by decide) weights141

private theorem weights142 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 25410 25665 = 102034021 := by
  decide +kernel

private theorem batch142 :
    (∑ n ∈ Finset.Icc 25410 25665, roundedTerm 10000000000 n) = 102034021 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 25410 25665 102034021
    (by decide) (by decide) weights142

private theorem weights143 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 25666 25921 = 101201271 := by
  decide +kernel

private theorem batch143 :
    (∑ n ∈ Finset.Icc 25666 25921, roundedTerm 10000000000 n) = 101201271 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 25666 25921 101201271
    (by decide) (by decide) weights143

private theorem weights144 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 25922 26177 = 96701389 := by
  decide +kernel

private theorem batch144 :
    (∑ n ∈ Finset.Icc 25922 26177, roundedTerm 10000000000 n) = 96701389 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 25922 26177 96701389
    (by decide) (by decide) weights144

private theorem weights145 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 26178 26433 = 97835010 := by
  decide +kernel

private theorem batch145 :
    (∑ n ∈ Finset.Icc 26178 26433, roundedTerm 10000000000 n) = 97835010 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 26178 26433 97835010
    (by decide) (by decide) weights145

private theorem weights146 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 26434 26534 = 38908739 := by
  decide +kernel

private theorem batch146 :
    (∑ n ∈ Finset.Icc 26434 26534, roundedTerm 10000000000 n) = 38908739 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 26434 26534 38908739
    (by decide) (by decide) weights146

private theorem weights147 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 26535 26790 = 96767627 := by
  decide +kernel

private theorem batch147 :
    (∑ n ∈ Finset.Icc 26535 26790, roundedTerm 10000000000 n) = 96767627 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 26535 26790 96767627
    (by decide) (by decide) weights147

private theorem weights148 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 26791 27046 = 94284698 := by
  decide +kernel

private theorem batch148 :
    (∑ n ∈ Finset.Icc 26791 27046, roundedTerm 10000000000 n) = 94284698 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 26791 27046 94284698
    (by decide) (by decide) weights148

private theorem weights149 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 27047 27302 = 95195270 := by
  decide +kernel

private theorem batch149 :
    (∑ n ∈ Finset.Icc 27047 27302, roundedTerm 10000000000 n) = 95195270 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 27047 27302 95195270
    (by decide) (by decide) weights149

private theorem weights150 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 27303 27558 = 94253201 := by
  decide +kernel

private theorem batch150 :
    (∑ n ∈ Finset.Icc 27303 27558, roundedTerm 10000000000 n) = 94253201 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 27303 27558 94253201
    (by decide) (by decide) weights150

private theorem weights151 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 27559 27814 = 94496551 := by
  decide +kernel

private theorem batch151 :
    (∑ n ∈ Finset.Icc 27559 27814, roundedTerm 10000000000 n) = 94496551 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 27559 27814 94496551
    (by decide) (by decide) weights151

private theorem weights152 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 27815 28070 = 88312146 := by
  decide +kernel

private theorem batch152 :
    (∑ n ∈ Finset.Icc 27815 28070, roundedTerm 10000000000 n) = 88312146 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 27815 28070 88312146
    (by decide) (by decide) weights152

private theorem weights153 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 28071 28326 = 90179516 := by
  decide +kernel

private theorem batch153 :
    (∑ n ∈ Finset.Icc 28071 28326, roundedTerm 10000000000 n) = 90179516 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 28071 28326 90179516
    (by decide) (by decide) weights153

private theorem weights154 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 28327 28582 = 91684795 := by
  decide +kernel

private theorem batch154 :
    (∑ n ∈ Finset.Icc 28327 28582, roundedTerm 10000000000 n) = 91684795 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 28327 28582 91684795
    (by decide) (by decide) weights154

private theorem weights155 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 28583 28838 = 87642441 := by
  decide +kernel

private theorem batch155 :
    (∑ n ∈ Finset.Icc 28583 28838, roundedTerm 10000000000 n) = 87642441 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 28583 28838 87642441
    (by decide) (by decide) weights155

private theorem weights156 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 28839 29094 = 90398140 := by
  decide +kernel

private theorem batch156 :
    (∑ n ∈ Finset.Icc 28839 29094, roundedTerm 10000000000 n) = 90398140 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 28839 29094 90398140
    (by decide) (by decide) weights156

private theorem weights157 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 29095 29350 = 88014046 := by
  decide +kernel

private theorem batch157 :
    (∑ n ∈ Finset.Icc 29095 29350, roundedTerm 10000000000 n) = 88014046 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 29095 29350 88014046
    (by decide) (by decide) weights157

private theorem weights158 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 29351 29606 = 87295616 := by
  decide +kernel

private theorem batch158 :
    (∑ n ∈ Finset.Icc 29351 29606, roundedTerm 10000000000 n) = 87295616 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 29351 29606 87295616
    (by decide) (by decide) weights158

private theorem weights159 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 29607 29862 = 84598220 := by
  decide +kernel

private theorem batch159 :
    (∑ n ∈ Finset.Icc 29607 29862, roundedTerm 10000000000 n) = 84598220 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 29607 29862 84598220
    (by decide) (by decide) weights159

set_option trace.profiler true in
private theorem weights160 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 29863 30118 = 85904555 := by
  decide +kernel

private theorem batch160 :
    (∑ n ∈ Finset.Icc 29863 30118, roundedTerm 10000000000 n) = 85904555 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 29863 30118 85904555
    (by decide) (by decide) weights160

private theorem weights161 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30119 30374 = 83322766 := by
  decide +kernel

private theorem batch161 :
    (∑ n ∈ Finset.Icc 30119 30374, roundedTerm 10000000000 n) = 83322766 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30119 30374 83322766
    (by decide) (by decide) weights161

private theorem weights162 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30375 30465 = 31421629 := by
  decide +kernel

private theorem batch162 :
    (∑ n ∈ Finset.Icc 30375 30465, roundedTerm 10000000000 n) = 31421629 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30375 30465 31421629
    (by decide) (by decide) weights162

private theorem weights163 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30466 30721 = 83443044 := by
  decide +kernel

private theorem batch163 :
    (∑ n ∈ Finset.Icc 30466 30721, roundedTerm 10000000000 n) = 83443044 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30466 30721 83443044
    (by decide) (by decide) weights163

private theorem weights164 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30722 30977 = 81674244 := by
  decide +kernel

private theorem batch164 :
    (∑ n ∈ Finset.Icc 30722 30977, roundedTerm 10000000000 n) = 81674244 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30722 30977 81674244
    (by decide) (by decide) weights164

private theorem weights165 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 30978 31233 = 81906926 := by
  decide +kernel

private theorem batch165 :
    (∑ n ∈ Finset.Icc 30978 31233, roundedTerm 10000000000 n) = 81906926 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 30978 31233 81906926
    (by decide) (by decide) weights165

private theorem weights166 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 31234 31489 = 79979107 := by
  decide +kernel

private theorem batch166 :
    (∑ n ∈ Finset.Icc 31234 31489, roundedTerm 10000000000 n) = 79979107 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 31234 31489 79979107
    (by decide) (by decide) weights166

private theorem weights167 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 31490 31745 = 81511538 := by
  decide +kernel

private theorem batch167 :
    (∑ n ∈ Finset.Icc 31490 31745, roundedTerm 10000000000 n) = 81511538 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 31490 31745 81511538
    (by decide) (by decide) weights167

private theorem weights168 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 31746 32001 = 80275914 := by
  decide +kernel

private theorem batch168 :
    (∑ n ∈ Finset.Icc 31746 32001, roundedTerm 10000000000 n) = 80275914 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 31746 32001 80275914
    (by decide) (by decide) weights168

private theorem weights169 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 32002 32257 = 78606007 := by
  decide +kernel

private theorem batch169 :
    (∑ n ∈ Finset.Icc 32002 32257, roundedTerm 10000000000 n) = 78606007 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 32002 32257 78606007
    (by decide) (by decide) weights169

private theorem weights170 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 32258 32513 = 79933012 := by
  decide +kernel

private theorem batch170 :
    (∑ n ∈ Finset.Icc 32258 32513, roundedTerm 10000000000 n) = 79933012 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 32258 32513 79933012
    (by decide) (by decide) weights170

private theorem weights171 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 32514 32769 = 79504176 := by
  decide +kernel

private theorem batch171 :
    (∑ n ∈ Finset.Icc 32514 32769, roundedTerm 10000000000 n) = 79504176 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 32514 32769 79504176
    (by decide) (by decide) weights171

private theorem weights172 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 32770 33025 = 76681151 := by
  decide +kernel

private theorem batch172 :
    (∑ n ∈ Finset.Icc 32770 33025, roundedTerm 10000000000 n) = 76681151 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 32770 33025 76681151
    (by decide) (by decide) weights172

private theorem weights173 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 33026 33281 = 76362242 := by
  decide +kernel

private theorem batch173 :
    (∑ n ∈ Finset.Icc 33026 33281, roundedTerm 10000000000 n) = 76362242 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 33026 33281 76362242
    (by decide) (by decide) weights173

private theorem weights174 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 33282 33537 = 78616172 := by
  decide +kernel

private theorem batch174 :
    (∑ n ∈ Finset.Icc 33282 33537, roundedTerm 10000000000 n) = 78616172 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 33282 33537 78616172
    (by decide) (by decide) weights174

private theorem weights175 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 33538 33793 = 76875894 := by
  decide +kernel

private theorem batch175 :
    (∑ n ∈ Finset.Icc 33538 33793, roundedTerm 10000000000 n) = 76875894 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 33538 33793 76875894
    (by decide) (by decide) weights175

private theorem weights176 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 33794 34049 = 76216916 := by
  decide +kernel

private theorem batch176 :
    (∑ n ∈ Finset.Icc 33794 34049, roundedTerm 10000000000 n) = 76216916 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 33794 34049 76216916
    (by decide) (by decide) weights176

private theorem weights177 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34050 34305 = 73723652 := by
  decide +kernel

private theorem batch177 :
    (∑ n ∈ Finset.Icc 34050 34305, roundedTerm 10000000000 n) = 73723652 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34050 34305 73723652
    (by decide) (by decide) weights177

private theorem weights178 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34306 34561 = 73602092 := by
  decide +kernel

private theorem batch178 :
    (∑ n ∈ Finset.Icc 34306 34561, roundedTerm 10000000000 n) = 73602092 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34306 34561 73602092
    (by decide) (by decide) weights178

private theorem weights179 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34562 34817 = 74186458 := by
  decide +kernel

private theorem batch179 :
    (∑ n ∈ Finset.Icc 34562 34817, roundedTerm 10000000000 n) = 74186458 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34562 34817 74186458
    (by decide) (by decide) weights179

private theorem weights180 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34818 34989 = 48670505 := by
  decide +kernel

private theorem batch180 :
    (∑ n ∈ Finset.Icc 34818 34989, roundedTerm 10000000000 n) = 48670505 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34818 34989 48670505
    (by decide) (by decide) weights180

private theorem weights181 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 34990 35245 = 73216499 := by
  decide +kernel

private theorem batch181 :
    (∑ n ∈ Finset.Icc 34990 35245, roundedTerm 10000000000 n) = 73216499 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 34990 35245 73216499
    (by decide) (by decide) weights181

private theorem weights182 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 35246 35501 = 70029195 := by
  decide +kernel

private theorem batch182 :
    (∑ n ∈ Finset.Icc 35246 35501, roundedTerm 10000000000 n) = 70029195 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 35246 35501 70029195
    (by decide) (by decide) weights182

private theorem weights183 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 35502 35757 = 72302290 := by
  decide +kernel

private theorem batch183 :
    (∑ n ∈ Finset.Icc 35502 35757, roundedTerm 10000000000 n) = 72302290 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 35502 35757 72302290
    (by decide) (by decide) weights183

private theorem weights184 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 35758 36013 = 73143217 := by
  decide +kernel

private theorem batch184 :
    (∑ n ∈ Finset.Icc 35758 36013, roundedTerm 10000000000 n) = 73143217 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 35758 36013 73143217
    (by decide) (by decide) weights184

private theorem weights185 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 36014 36269 = 71343939 := by
  decide +kernel

private theorem batch185 :
    (∑ n ∈ Finset.Icc 36014 36269, roundedTerm 10000000000 n) = 71343939 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 36014 36269 71343939
    (by decide) (by decide) weights185

private theorem weights186 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 36270 36525 = 70123751 := by
  decide +kernel

private theorem batch186 :
    (∑ n ∈ Finset.Icc 36270 36525, roundedTerm 10000000000 n) = 70123751 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 36270 36525 70123751
    (by decide) (by decide) weights186

private theorem weights187 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 36526 36781 = 70779459 := by
  decide +kernel

private theorem batch187 :
    (∑ n ∈ Finset.Icc 36526 36781, roundedTerm 10000000000 n) = 70779459 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 36526 36781 70779459
    (by decide) (by decide) weights187

private theorem weights188 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 36782 37037 = 67511995 := by
  decide +kernel

private theorem batch188 :
    (∑ n ∈ Finset.Icc 36782 37037, roundedTerm 10000000000 n) = 67511995 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 36782 37037 67511995
    (by decide) (by decide) weights188

private theorem weights189 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 37038 37293 = 69133610 := by
  decide +kernel

private theorem batch189 :
    (∑ n ∈ Finset.Icc 37038 37293, roundedTerm 10000000000 n) = 69133610 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 37038 37293 69133610
    (by decide) (by decide) weights189

private theorem weights190 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 37294 37549 = 66602734 := by
  decide +kernel

private theorem batch190 :
    (∑ n ∈ Finset.Icc 37294 37549, roundedTerm 10000000000 n) = 66602734 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 37294 37549 66602734
    (by decide) (by decide) weights190

private theorem weights191 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 37550 37805 = 67819251 := by
  decide +kernel

private theorem batch191 :
    (∑ n ∈ Finset.Icc 37550 37805, roundedTerm 10000000000 n) = 67819251 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 37550 37805 67819251
    (by decide) (by decide) weights191

set_option trace.profiler true in
private theorem weights192 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 37806 38061 = 69053028 := by
  decide +kernel

private theorem batch192 :
    (∑ n ∈ Finset.Icc 37806 38061, roundedTerm 10000000000 n) = 69053028 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 37806 38061 69053028
    (by decide) (by decide) weights192

private theorem weights193 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 38062 38317 = 68018157 := by
  decide +kernel

private theorem batch193 :
    (∑ n ∈ Finset.Icc 38062 38317, roundedTerm 10000000000 n) = 68018157 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 38062 38317 68018157
    (by decide) (by decide) weights193

private theorem weights194 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 38318 38573 = 66333748 := by
  decide +kernel

private theorem batch194 :
    (∑ n ∈ Finset.Icc 38318 38573, roundedTerm 10000000000 n) = 66333748 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 38318 38573 66333748
    (by decide) (by decide) weights194

private theorem weights195 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 38574 38829 = 63843221 := by
  decide +kernel

private theorem batch195 :
    (∑ n ∈ Finset.Icc 38574 38829, roundedTerm 10000000000 n) = 63843221 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 38574 38829 63843221
    (by decide) (by decide) weights195

private theorem weights196 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 38830 39085 = 64589544 := by
  decide +kernel

private theorem batch196 :
    (∑ n ∈ Finset.Icc 38830 39085, roundedTerm 10000000000 n) = 64589544 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 38830 39085 64589544
    (by decide) (by decide) weights196

private theorem weights197 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 39086 39341 = 66638019 := by
  decide +kernel

private theorem batch197 :
    (∑ n ∈ Finset.Icc 39086 39341, roundedTerm 10000000000 n) = 66638019 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 39086 39341 66638019
    (by decide) (by decide) weights197

private theorem weights198 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 39342 39597 = 64431036 := by
  decide +kernel

private theorem batch198 :
    (∑ n ∈ Finset.Icc 39342 39597, roundedTerm 10000000000 n) = 64431036 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 39342 39597 64431036
    (by decide) (by decide) weights198

private theorem weights199 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 39598 39853 = 64599569 := by
  decide +kernel

private theorem batch199 :
    (∑ n ∈ Finset.Icc 39598 39853, roundedTerm 10000000000 n) = 64599569 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 39598 39853 64599569
    (by decide) (by decide) weights199

private theorem weights200 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 39854 40109 = 63590007 := by
  decide +kernel

private theorem batch200 :
    (∑ n ∈ Finset.Icc 39854 40109, roundedTerm 10000000000 n) = 63590007 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 39854 40109 63590007
    (by decide) (by decide) weights200

private theorem weights201 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 40110 40190 = 21190034 := by
  decide +kernel

private theorem batch201 :
    (∑ n ∈ Finset.Icc 40110 40190, roundedTerm 10000000000 n) = 21190034 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 40110 40190 21190034
    (by decide) (by decide) weights201

private theorem weights202 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 40191 40446 = 62965214 := by
  decide +kernel

private theorem batch202 :
    (∑ n ∈ Finset.Icc 40191 40446, roundedTerm 10000000000 n) = 62965214 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 40191 40446 62965214
    (by decide) (by decide) weights202

private theorem weights203 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 40447 40702 = 63410299 := by
  decide +kernel

private theorem batch203 :
    (∑ n ∈ Finset.Icc 40447 40702, roundedTerm 10000000000 n) = 63410299 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 40447 40702 63410299
    (by decide) (by decide) weights203

private theorem weights204 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 40703 40958 = 62617042 := by
  decide +kernel

private theorem batch204 :
    (∑ n ∈ Finset.Icc 40703 40958, roundedTerm 10000000000 n) = 62617042 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 40703 40958 62617042
    (by decide) (by decide) weights204

private theorem weights205 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 40959 41214 = 62682730 := by
  decide +kernel

private theorem batch205 :
    (∑ n ∈ Finset.Icc 40959 41214, roundedTerm 10000000000 n) = 62682730 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 40959 41214 62682730
    (by decide) (by decide) weights205

private theorem weights206 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 41215 41470 = 61255500 := by
  decide +kernel

private theorem batch206 :
    (∑ n ∈ Finset.Icc 41215 41470, roundedTerm 10000000000 n) = 61255500 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 41215 41470 61255500
    (by decide) (by decide) weights206

private theorem weights207 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 41471 41726 = 62616196 := by
  decide +kernel

private theorem batch207 :
    (∑ n ∈ Finset.Icc 41471 41726, roundedTerm 10000000000 n) = 62616196 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 41471 41726 62616196
    (by decide) (by decide) weights207

private theorem weights208 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 41727 41982 = 62269740 := by
  decide +kernel

private theorem batch208 :
    (∑ n ∈ Finset.Icc 41727 41982, roundedTerm 10000000000 n) = 62269740 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 41727 41982 62269740
    (by decide) (by decide) weights208

private theorem weights209 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 41983 42238 = 59976859 := by
  decide +kernel

private theorem batch209 :
    (∑ n ∈ Finset.Icc 41983 42238, roundedTerm 10000000000 n) = 59976859 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 41983 42238 59976859
    (by decide) (by decide) weights209

private theorem weights210 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 42239 42494 = 61087295 := by
  decide +kernel

private theorem batch210 :
    (∑ n ∈ Finset.Icc 42239 42494, roundedTerm 10000000000 n) = 61087295 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 42239 42494 61087295
    (by decide) (by decide) weights210

private theorem weights211 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 42495 42750 = 61107721 := by
  decide +kernel

private theorem batch211 :
    (∑ n ∈ Finset.Icc 42495 42750, roundedTerm 10000000000 n) = 61107721 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 42495 42750 61107721
    (by decide) (by decide) weights211

private theorem weights212 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 42751 43006 = 60218071 := by
  decide +kernel

private theorem batch212 :
    (∑ n ∈ Finset.Icc 42751 43006, roundedTerm 10000000000 n) = 60218071 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 42751 43006 60218071
    (by decide) (by decide) weights212

private theorem weights213 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 43007 43262 = 59672803 := by
  decide +kernel

private theorem batch213 :
    (∑ n ∈ Finset.Icc 43007 43262, roundedTerm 10000000000 n) = 59672803 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 43007 43262 59672803
    (by decide) (by decide) weights213

private theorem weights214 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 43263 43518 = 59342670 := by
  decide +kernel

private theorem batch214 :
    (∑ n ∈ Finset.Icc 43263 43518, roundedTerm 10000000000 n) = 59342670 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 43263 43518 59342670
    (by decide) (by decide) weights214

private theorem weights215 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 43519 43774 = 58706992 := by
  decide +kernel

private theorem batch215 :
    (∑ n ∈ Finset.Icc 43519 43774, roundedTerm 10000000000 n) = 58706992 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 43519 43774 58706992
    (by decide) (by decide) weights215

private theorem weights216 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 43775 44030 = 58614023 := by
  decide +kernel

private theorem batch216 :
    (∑ n ∈ Finset.Icc 43775 44030, roundedTerm 10000000000 n) = 58614023 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 43775 44030 58614023
    (by decide) (by decide) weights216

private theorem weights217 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 44031 44286 = 56748687 := by
  decide +kernel

private theorem batch217 :
    (∑ n ∈ Finset.Icc 44031 44286, roundedTerm 10000000000 n) = 56748687 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 44031 44286 56748687
    (by decide) (by decide) weights217

private theorem weights218 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 44287 44542 = 57727724 := by
  decide +kernel

private theorem batch218 :
    (∑ n ∈ Finset.Icc 44287 44542, roundedTerm 10000000000 n) = 57727724 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 44287 44542 57727724
    (by decide) (by decide) weights218

private theorem weights219 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 44543 44798 = 57803673 := by
  decide +kernel

private theorem batch219 :
    (∑ n ∈ Finset.Icc 44543 44798, roundedTerm 10000000000 n) = 57803673 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 44543 44798 57803673
    (by decide) (by decide) weights219

private theorem weights220 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 44799 45054 = 56385097 := by
  decide +kernel

private theorem batch220 :
    (∑ n ∈ Finset.Icc 44799 45054, roundedTerm 10000000000 n) = 56385097 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 44799 45054 56385097
    (by decide) (by decide) weights220

private theorem weights221 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 45055 45310 = 57010852 := by
  decide +kernel

private theorem batch221 :
    (∑ n ∈ Finset.Icc 45055 45310, roundedTerm 10000000000 n) = 57010852 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 45055 45310 57010852
    (by decide) (by decide) weights221

private theorem weights222 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 45311 45566 = 58027300 := by
  decide +kernel

private theorem batch222 :
    (∑ n ∈ Finset.Icc 45311 45566, roundedTerm 10000000000 n) = 58027300 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 45311 45566 58027300
    (by decide) (by decide) weights222

private theorem weights223 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 45567 45822 = 55633192 := by
  decide +kernel

private theorem batch223 :
    (∑ n ∈ Finset.Icc 45567 45822, roundedTerm 10000000000 n) = 55633192 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 45567 45822 55633192
    (by decide) (by decide) weights223

set_option trace.profiler true in
private theorem weights224 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 45823 46078 = 55778081 := by
  decide +kernel

private theorem batch224 :
    (∑ n ∈ Finset.Icc 45823 46078, roundedTerm 10000000000 n) = 55778081 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 45823 46078 55778081
    (by decide) (by decide) weights224

private theorem weights225 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46079 46144 = 14287304 := by
  decide +kernel

private theorem batch225 :
    (∑ n ∈ Finset.Icc 46079 46144, roundedTerm 10000000000 n) = 14287304 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46079 46144 14287304
    (by decide) (by decide) weights225

private theorem weights226 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46145 46400 = 55398756 := by
  decide +kernel

private theorem batch226 :
    (∑ n ∈ Finset.Icc 46145 46400, roundedTerm 10000000000 n) = 55398756 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46145 46400 55398756
    (by decide) (by decide) weights226

private theorem weights227 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46401 46656 = 55697240 := by
  decide +kernel

private theorem batch227 :
    (∑ n ∈ Finset.Icc 46401 46656, roundedTerm 10000000000 n) = 55697240 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46401 46656 55697240
    (by decide) (by decide) weights227

private theorem weights228 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46657 46912 = 56336150 := by
  decide +kernel

private theorem batch228 :
    (∑ n ∈ Finset.Icc 46657 46912, roundedTerm 10000000000 n) = 56336150 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46657 46912 56336150
    (by decide) (by decide) weights228

private theorem weights229 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 46913 47168 = 54056855 := by
  decide +kernel

private theorem batch229 :
    (∑ n ∈ Finset.Icc 46913 47168, roundedTerm 10000000000 n) = 54056855 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 46913 47168 54056855
    (by decide) (by decide) weights229

private theorem weights230 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 47169 47424 = 54993569 := by
  decide +kernel

private theorem batch230 :
    (∑ n ∈ Finset.Icc 47169 47424, roundedTerm 10000000000 n) = 54993569 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 47169 47424 54993569
    (by decide) (by decide) weights230

private theorem weights231 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 47425 47680 = 52514899 := by
  decide +kernel

private theorem batch231 :
    (∑ n ∈ Finset.Icc 47425 47680, roundedTerm 10000000000 n) = 52514899 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 47425 47680 52514899
    (by decide) (by decide) weights231

private theorem weights232 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 47681 47936 = 53479331 := by
  decide +kernel

private theorem batch232 :
    (∑ n ∈ Finset.Icc 47681 47936, roundedTerm 10000000000 n) = 53479331 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 47681 47936 53479331
    (by decide) (by decide) weights232

private theorem weights233 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 47937 48192 = 52610236 := by
  decide +kernel

private theorem batch233 :
    (∑ n ∈ Finset.Icc 47937 48192, roundedTerm 10000000000 n) = 52610236 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 47937 48192 52610236
    (by decide) (by decide) weights233

private theorem weights234 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 48193 48448 = 52694840 := by
  decide +kernel

private theorem batch234 :
    (∑ n ∈ Finset.Icc 48193 48448, roundedTerm 10000000000 n) = 52694840 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 48193 48448 52694840
    (by decide) (by decide) weights234

private theorem weights235 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 48449 48704 = 52529069 := by
  decide +kernel

private theorem batch235 :
    (∑ n ∈ Finset.Icc 48449 48704, roundedTerm 10000000000 n) = 52529069 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 48449 48704 52529069
    (by decide) (by decide) weights235

private theorem weights236 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 48705 48960 = 52345146 := by
  decide +kernel

private theorem batch236 :
    (∑ n ∈ Finset.Icc 48705 48960, roundedTerm 10000000000 n) = 52345146 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 48705 48960 52345146
    (by decide) (by decide) weights236

private theorem weights237 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 48961 49216 = 52184386 := by
  decide +kernel

private theorem batch237 :
    (∑ n ∈ Finset.Icc 48961 49216, roundedTerm 10000000000 n) = 52184386 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 48961 49216 52184386
    (by decide) (by decide) weights237

private theorem weights238 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 49217 49472 = 52034752 := by
  decide +kernel

private theorem batch238 :
    (∑ n ∈ Finset.Icc 49217 49472, roundedTerm 10000000000 n) = 52034752 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 49217 49472 52034752
    (by decide) (by decide) weights238

private theorem weights239 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 49473 49728 = 50759454 := by
  decide +kernel

private theorem batch239 :
    (∑ n ∈ Finset.Icc 49473 49728, roundedTerm 10000000000 n) = 50759454 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 49473 49728 50759454
    (by decide) (by decide) weights239

private theorem weights240 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 49729 49984 = 51812320 := by
  decide +kernel

private theorem batch240 :
    (∑ n ∈ Finset.Icc 49729 49984, roundedTerm 10000000000 n) = 51812320 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 49729 49984 51812320
    (by decide) (by decide) weights240

private theorem weights241 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 49985 50240 = 52207458 := by
  decide +kernel

private theorem batch241 :
    (∑ n ∈ Finset.Icc 49985 50240, roundedTerm 10000000000 n) = 52207458 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 49985 50240 52207458
    (by decide) (by decide) weights241

private theorem weights242 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 50241 50496 = 48961788 := by
  decide +kernel

private theorem batch242 :
    (∑ n ∈ Finset.Icc 50241 50496, roundedTerm 10000000000 n) = 48961788 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 50241 50496 48961788
    (by decide) (by decide) weights242

private theorem weights243 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 50497 50752 = 51191196 := by
  decide +kernel

private theorem batch243 :
    (∑ n ∈ Finset.Icc 50497 50752, roundedTerm 10000000000 n) = 51191196 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 50497 50752 51191196
    (by decide) (by decide) weights243

private theorem weights244 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 50753 51008 = 51177519 := by
  decide +kernel

private theorem batch244 :
    (∑ n ∈ Finset.Icc 50753 51008, roundedTerm 10000000000 n) = 51177519 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 50753 51008 51177519
    (by decide) (by decide) weights244

private theorem weights245 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 51009 51264 = 49001997 := by
  decide +kernel

private theorem batch245 :
    (∑ n ∈ Finset.Icc 51009 51264, roundedTerm 10000000000 n) = 49001997 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 51009 51264 49001997
    (by decide) (by decide) weights245

private theorem weights246 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 51265 51520 = 50932507 := by
  decide +kernel

private theorem batch246 :
    (∑ n ∈ Finset.Icc 51265 51520, roundedTerm 10000000000 n) = 50932507 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 51265 51520 50932507
    (by decide) (by decide) weights246

private theorem weights247 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 51521 51776 = 50072294 := by
  decide +kernel

private theorem batch247 :
    (∑ n ∈ Finset.Icc 51521 51776, roundedTerm 10000000000 n) = 50072294 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 51521 51776 50072294
    (by decide) (by decide) weights247

private theorem weights248 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 51777 52032 = 49835077 := by
  decide +kernel

private theorem batch248 :
    (∑ n ∈ Finset.Icc 51777 52032, roundedTerm 10000000000 n) = 49835077 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 51777 52032 49835077
    (by decide) (by decide) weights248

private theorem weights249 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 52033 52288 = 47884001 := by
  decide +kernel

private theorem batch249 :
    (∑ n ∈ Finset.Icc 52033 52288, roundedTerm 10000000000 n) = 47884001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 52033 52288 47884001
    (by decide) (by decide) weights249

private theorem weights250 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 52289 52544 = 48729438 := by
  decide +kernel

private theorem batch250 :
    (∑ n ∈ Finset.Icc 52289 52544, roundedTerm 10000000000 n) = 48729438 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 52289 52544 48729438
    (by decide) (by decide) weights250

private theorem weights251 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 52545 52800 = 48929459 := by
  decide +kernel

private theorem batch251 :
    (∑ n ∈ Finset.Icc 52545 52800, roundedTerm 10000000000 n) = 48929459 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 52545 52800 48929459
    (by decide) (by decide) weights251

private theorem weights252 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 52801 52976 = 33057438 := by
  decide +kernel

private theorem batch252 :
    (∑ n ∈ Finset.Icc 52801 52976, roundedTerm 10000000000 n) = 33057438 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 52801 52976 33057438
    (by decide) (by decide) weights252

private theorem weights253 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 52977 53232 = 47515943 := by
  decide +kernel

private theorem batch253 :
    (∑ n ∈ Finset.Icc 52977 53232, roundedTerm 10000000000 n) = 47515943 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 52977 53232 47515943
    (by decide) (by decide) weights253

private theorem weights254 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 53233 53488 = 47385780 := by
  decide +kernel

private theorem batch254 :
    (∑ n ∈ Finset.Icc 53233 53488, roundedTerm 10000000000 n) = 47385780 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 53233 53488 47385780
    (by decide) (by decide) weights254

private theorem weights255 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 53489 53744 = 48789929 := by
  decide +kernel

private theorem batch255 :
    (∑ n ∈ Finset.Icc 53489 53744, roundedTerm 10000000000 n) = 48789929 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 53489 53744 48789929
    (by decide) (by decide) weights255

set_option trace.profiler true in
private theorem weights256 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 53745 54000 = 46775237 := by
  decide +kernel

private theorem batch256 :
    (∑ n ∈ Finset.Icc 53745 54000, roundedTerm 10000000000 n) = 46775237 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 53745 54000 46775237
    (by decide) (by decide) weights256

private theorem weights257 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 54001 54256 = 47970488 := by
  decide +kernel

private theorem batch257 :
    (∑ n ∈ Finset.Icc 54001 54256, roundedTerm 10000000000 n) = 47970488 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 54001 54256 47970488
    (by decide) (by decide) weights257

private theorem weights258 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 54257 54512 = 48066858 := by
  decide +kernel

private theorem batch258 :
    (∑ n ∈ Finset.Icc 54257 54512, roundedTerm 10000000000 n) = 48066858 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 54257 54512 48066858
    (by decide) (by decide) weights258

private theorem weights259 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 54513 54768 = 47202653 := by
  decide +kernel

private theorem batch259 :
    (∑ n ∈ Finset.Icc 54513 54768, roundedTerm 10000000000 n) = 47202653 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 54513 54768 47202653
    (by decide) (by decide) weights259

private theorem weights260 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 54769 55024 = 46042637 := by
  decide +kernel

private theorem batch260 :
    (∑ n ∈ Finset.Icc 54769 55024, roundedTerm 10000000000 n) = 46042637 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 54769 55024 46042637
    (by decide) (by decide) weights260

private theorem weights261 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 55025 55280 = 46261098 := by
  decide +kernel

private theorem batch261 :
    (∑ n ∈ Finset.Icc 55025 55280, roundedTerm 10000000000 n) = 46261098 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 55025 55280 46261098
    (by decide) (by decide) weights261

private theorem weights262 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 55281 55536 = 45716142 := by
  decide +kernel

private theorem batch262 :
    (∑ n ∈ Finset.Icc 55281 55536, roundedTerm 10000000000 n) = 45716142 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 55281 55536 45716142
    (by decide) (by decide) weights262

private theorem weights263 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 55537 55792 = 44133985 := by
  decide +kernel

private theorem batch263 :
    (∑ n ∈ Finset.Icc 55537 55792, roundedTerm 10000000000 n) = 44133985 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 55537 55792 44133985
    (by decide) (by decide) weights263

private theorem weights264 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 55793 56048 = 46198331 := by
  decide +kernel

private theorem batch264 :
    (∑ n ∈ Finset.Icc 55793 56048, roundedTerm 10000000000 n) = 46198331 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 55793 56048 46198331
    (by decide) (by decide) weights264

private theorem weights265 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 56049 56304 = 45760728 := by
  decide +kernel

private theorem batch265 :
    (∑ n ∈ Finset.Icc 56049 56304, roundedTerm 10000000000 n) = 45760728 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 56049 56304 45760728
    (by decide) (by decide) weights265

private theorem weights266 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 56305 56560 = 44532061 := by
  decide +kernel

private theorem batch266 :
    (∑ n ∈ Finset.Icc 56305 56560, roundedTerm 10000000000 n) = 44532061 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 56305 56560 44532061
    (by decide) (by decide) weights266

private theorem weights267 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 56561 56816 = 45513458 := by
  decide +kernel

private theorem batch267 :
    (∑ n ∈ Finset.Icc 56561 56816, roundedTerm 10000000000 n) = 45513458 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 56561 56816 45513458
    (by decide) (by decide) weights267

private theorem weights268 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 56817 57072 = 45009904 := by
  decide +kernel

private theorem batch268 :
    (∑ n ∈ Finset.Icc 56817 57072, roundedTerm 10000000000 n) = 45009904 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 56817 57072 45009904
    (by decide) (by decide) weights268

private theorem weights269 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 57073 57328 = 44608001 := by
  decide +kernel

private theorem batch269 :
    (∑ n ∈ Finset.Icc 57073 57328, roundedTerm 10000000000 n) = 44608001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 57073 57328 44608001
    (by decide) (by decide) weights269

private theorem weights270 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 57329 57584 = 43461989 := by
  decide +kernel

private theorem batch270 :
    (∑ n ∈ Finset.Icc 57329 57584, roundedTerm 10000000000 n) = 43461989 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 57329 57584 43461989
    (by decide) (by decide) weights270

private theorem weights271 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 57585 57840 = 45707674 := by
  decide +kernel

private theorem batch271 :
    (∑ n ∈ Finset.Icc 57585 57840, roundedTerm 10000000000 n) = 45707674 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 57585 57840 45707674
    (by decide) (by decide) weights271

private theorem weights272 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 57841 58096 = 44034700 := by
  decide +kernel

private theorem batch272 :
    (∑ n ∈ Finset.Icc 57841 58096, roundedTerm 10000000000 n) = 44034700 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 57841 58096 44034700
    (by decide) (by decide) weights272

private theorem weights273 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 58097 58352 = 43591524 := by
  decide +kernel

private theorem batch273 :
    (∑ n ∈ Finset.Icc 58097 58352, roundedTerm 10000000000 n) = 43591524 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 58097 58352 43591524
    (by decide) (by decide) weights273

private theorem weights274 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 58353 58608 = 43587599 := by
  decide +kernel

private theorem batch274 :
    (∑ n ∈ Finset.Icc 58353 58608, roundedTerm 10000000000 n) = 43587599 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 58353 58608 43587599
    (by decide) (by decide) weights274

private theorem weights275 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 58609 58864 = 43540012 := by
  decide +kernel

private theorem batch275 :
    (∑ n ∈ Finset.Icc 58609 58864, roundedTerm 10000000000 n) = 43540012 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 58609 58864 43540012
    (by decide) (by decide) weights275

private theorem weights276 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 58865 59120 = 44398095 := by
  decide +kernel

private theorem batch276 :
    (∑ n ∈ Finset.Icc 58865 59120, roundedTerm 10000000000 n) = 44398095 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 58865 59120 44398095
    (by decide) (by decide) weights276

private theorem weights277 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 59121 59376 = 42937333 := by
  decide +kernel

private theorem batch277 :
    (∑ n ∈ Finset.Icc 59121 59376, roundedTerm 10000000000 n) = 42937333 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 59121 59376 42937333
    (by decide) (by decide) weights277

private theorem weights278 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 59377 59632 = 43869039 := by
  decide +kernel

private theorem batch278 :
    (∑ n ∈ Finset.Icc 59377 59632, roundedTerm 10000000000 n) = 43869039 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 59377 59632 43869039
    (by decide) (by decide) weights278

private theorem weights279 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 59633 59888 = 41201000 := by
  decide +kernel

private theorem batch279 :
    (∑ n ∈ Finset.Icc 59633 59888, roundedTerm 10000000000 n) = 41201000 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 59633 59888 41201000
    (by decide) (by decide) weights279

private theorem weights280 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 59889 60144 = 43841351 := by
  decide +kernel

private theorem batch280 :
    (∑ n ∈ Finset.Icc 59889 60144, roundedTerm 10000000000 n) = 43841351 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 59889 60144 43841351
    (by decide) (by decide) weights280

private theorem weights281 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 60145 60400 = 41208121 := by
  decide +kernel

private theorem batch281 :
    (∑ n ∈ Finset.Icc 60145 60400, roundedTerm 10000000000 n) = 41208121 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 60145 60400 41208121
    (by decide) (by decide) weights281

private theorem weights282 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 60401 60656 = 43145648 := by
  decide +kernel

private theorem batch282 :
    (∑ n ∈ Finset.Icc 60401 60656, roundedTerm 10000000000 n) = 43145648 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 60401 60656 43145648
    (by decide) (by decide) weights282

private theorem weights283 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 60657 60832 = 28759248 := by
  decide +kernel

private theorem batch283 :
    (∑ n ∈ Finset.Icc 60657 60832, roundedTerm 10000000000 n) = 28759248 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 60657 60832 28759248
    (by decide) (by decide) weights283

private theorem weights284 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 60833 61088 = 42304125 := by
  decide +kernel

private theorem batch284 :
    (∑ n ∈ Finset.Icc 60833 61088, roundedTerm 10000000000 n) = 42304125 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 60833 61088 42304125
    (by decide) (by decide) weights284

private theorem weights285 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 61089 61344 = 42443978 := by
  decide +kernel

private theorem batch285 :
    (∑ n ∈ Finset.Icc 61089 61344, roundedTerm 10000000000 n) = 42443978 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 61089 61344 42443978
    (by decide) (by decide) weights285

private theorem weights286 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 61345 61600 = 41430460 := by
  decide +kernel

private theorem batch286 :
    (∑ n ∈ Finset.Icc 61345 61600, roundedTerm 10000000000 n) = 41430460 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 61345 61600 41430460
    (by decide) (by decide) weights286

private theorem weights287 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 61601 61856 = 40659192 := by
  decide +kernel

private theorem batch287 :
    (∑ n ∈ Finset.Icc 61601 61856, roundedTerm 10000000000 n) = 40659192 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 61601 61856 40659192
    (by decide) (by decide) weights287

set_option trace.profiler true in
private theorem weights288 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 61857 62112 = 41990843 := by
  decide +kernel

private theorem batch288 :
    (∑ n ∈ Finset.Icc 61857 62112, roundedTerm 10000000000 n) = 41990843 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 61857 62112 41990843
    (by decide) (by decide) weights288

private theorem weights289 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 62113 62368 = 41359918 := by
  decide +kernel

private theorem batch289 :
    (∑ n ∈ Finset.Icc 62113 62368, roundedTerm 10000000000 n) = 41359918 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 62113 62368 41359918
    (by decide) (by decide) weights289

private theorem weights290 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 62369 62624 = 40883419 := by
  decide +kernel

private theorem batch290 :
    (∑ n ∈ Finset.Icc 62369 62624, roundedTerm 10000000000 n) = 40883419 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 62369 62624 40883419
    (by decide) (by decide) weights290

private theorem weights291 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 62625 62880 = 39433339 := by
  decide +kernel

private theorem batch291 :
    (∑ n ∈ Finset.Icc 62625 62880, roundedTerm 10000000000 n) = 39433339 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 62625 62880 39433339
    (by decide) (by decide) weights291

private theorem weights292 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 62881 63136 = 40948357 := by
  decide +kernel

private theorem batch292 :
    (∑ n ∈ Finset.Icc 62881 63136, roundedTerm 10000000000 n) = 40948357 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 62881 63136 40948357
    (by decide) (by decide) weights292

private theorem weights293 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 63137 63392 = 40306543 := by
  decide +kernel

private theorem batch293 :
    (∑ n ∈ Finset.Icc 63137 63392, roundedTerm 10000000000 n) = 40306543 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 63137 63392 40306543
    (by decide) (by decide) weights293

private theorem weights294 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 63393 63648 = 41049866 := by
  decide +kernel

private theorem batch294 :
    (∑ n ∈ Finset.Icc 63393 63648, roundedTerm 10000000000 n) = 41049866 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 63393 63648 41049866
    (by decide) (by decide) weights294

private theorem weights295 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 63649 63904 = 39362074 := by
  decide +kernel

private theorem batch295 :
    (∑ n ∈ Finset.Icc 63649 63904, roundedTerm 10000000000 n) = 39362074 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 63649 63904 39362074
    (by decide) (by decide) weights295

private theorem weights296 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 63905 64160 = 39649859 := by
  decide +kernel

private theorem batch296 :
    (∑ n ∈ Finset.Icc 63905 64160, roundedTerm 10000000000 n) = 39649859 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 63905 64160 39649859
    (by decide) (by decide) weights296

private theorem weights297 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 64161 64416 = 40665015 := by
  decide +kernel

private theorem batch297 :
    (∑ n ∈ Finset.Icc 64161 64416, roundedTerm 10000000000 n) = 40665015 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 64161 64416 40665015
    (by decide) (by decide) weights297

private theorem weights298 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 64417 64672 = 38997169 := by
  decide +kernel

private theorem batch298 :
    (∑ n ∈ Finset.Icc 64417 64672, roundedTerm 10000000000 n) = 38997169 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 64417 64672 38997169
    (by decide) (by decide) weights298

private theorem weights299 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 64673 64928 = 39881411 := by
  decide +kernel

private theorem batch299 :
    (∑ n ∈ Finset.Icc 64673 64928, roundedTerm 10000000000 n) = 39881411 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 64673 64928 39881411
    (by decide) (by decide) weights299

private theorem weights300 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 64929 65184 = 38841177 := by
  decide +kernel

private theorem batch300 :
    (∑ n ∈ Finset.Icc 64929 65184, roundedTerm 10000000000 n) = 38841177 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 64929 65184 38841177
    (by decide) (by decide) weights300

private theorem weights301 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 65185 65440 = 39851876 := by
  decide +kernel

private theorem batch301 :
    (∑ n ∈ Finset.Icc 65185 65440, roundedTerm 10000000000 n) = 39851876 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 65185 65440 39851876
    (by decide) (by decide) weights301

private theorem weights302 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 65441 65696 = 38351304 := by
  decide +kernel

private theorem batch302 :
    (∑ n ∈ Finset.Icc 65441 65696, roundedTerm 10000000000 n) = 38351304 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 65441 65696 38351304
    (by decide) (by decide) weights302

private theorem weights303 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 65697 65952 = 38404310 := by
  decide +kernel

private theorem batch303 :
    (∑ n ∈ Finset.Icc 65697 65952, roundedTerm 10000000000 n) = 38404310 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 65697 65952 38404310
    (by decide) (by decide) weights303

private theorem weights304 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 65953 66208 = 38889418 := by
  decide +kernel

private theorem batch304 :
    (∑ n ∈ Finset.Icc 65953 66208, roundedTerm 10000000000 n) = 38889418 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 65953 66208 38889418
    (by decide) (by decide) weights304

private theorem weights305 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 66209 66464 = 38727906 := by
  decide +kernel

private theorem batch305 :
    (∑ n ∈ Finset.Icc 66209 66464, roundedTerm 10000000000 n) = 38727906 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 66209 66464 38727906
    (by decide) (by decide) weights305

private theorem weights306 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 66465 66720 = 38574413 := by
  decide +kernel

private theorem batch306 :
    (∑ n ∈ Finset.Icc 66465 66720, roundedTerm 10000000000 n) = 38574413 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 66465 66720 38574413
    (by decide) (by decide) weights306

private theorem weights307 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 66721 66976 = 37908451 := by
  decide +kernel

private theorem batch307 :
    (∑ n ∈ Finset.Icc 66721 66976, roundedTerm 10000000000 n) = 37908451 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 66721 66976 37908451
    (by decide) (by decide) weights307

private theorem weights308 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 66977 67232 = 38030454 := by
  decide +kernel

private theorem batch308 :
    (∑ n ∈ Finset.Icc 66977 67232, roundedTerm 10000000000 n) = 38030454 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 66977 67232 38030454
    (by decide) (by decide) weights308

private theorem weights309 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 67233 67488 = 37713340 := by
  decide +kernel

private theorem batch309 :
    (∑ n ∈ Finset.Icc 67233 67488, roundedTerm 10000000000 n) = 37713340 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 67233 67488 37713340
    (by decide) (by decide) weights309

private theorem weights310 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 67489 67744 = 38441569 := by
  decide +kernel

private theorem batch310 :
    (∑ n ∈ Finset.Icc 67489 67744, roundedTerm 10000000000 n) = 38441569 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 67489 67744 38441569
    (by decide) (by decide) weights310

private theorem weights311 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 67745 68000 = 38534151 := by
  decide +kernel

private theorem batch311 :
    (∑ n ∈ Finset.Icc 67745 68000, roundedTerm 10000000000 n) = 38534151 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 67745 68000 38534151
    (by decide) (by decide) weights311

private theorem weights312 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 68001 68256 = 37733330 := by
  decide +kernel

private theorem batch312 :
    (∑ n ∈ Finset.Icc 68001 68256, roundedTerm 10000000000 n) = 37733330 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 68001 68256 37733330
    (by decide) (by decide) weights312

private theorem weights313 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 68257 68512 = 37120072 := by
  decide +kernel

private theorem batch313 :
    (∑ n ∈ Finset.Icc 68257 68512, roundedTerm 10000000000 n) = 37120072 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 68257 68512 37120072
    (by decide) (by decide) weights313

private theorem weights314 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 68513 68768 = 37080671 := by
  decide +kernel

private theorem batch314 :
    (∑ n ∈ Finset.Icc 68513 68768, roundedTerm 10000000000 n) = 37080671 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 68513 68768 37080671
    (by decide) (by decide) weights314

private theorem weights315 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 68769 69024 = 35992201 := by
  decide +kernel

private theorem batch315 :
    (∑ n ∈ Finset.Icc 68769 69024, roundedTerm 10000000000 n) = 35992201 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 68769 69024 35992201
    (by decide) (by decide) weights315

private theorem weights316 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 69025 69280 = 37133549 := by
  decide +kernel

private theorem batch316 :
    (∑ n ∈ Finset.Icc 69025 69280, roundedTerm 10000000000 n) = 37133549 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 69025 69280 37133549
    (by decide) (by decide) weights316

private theorem weights317 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 69281 69536 = 36134437 := by
  decide +kernel

private theorem batch317 :
    (∑ n ∈ Finset.Icc 69281 69536, roundedTerm 10000000000 n) = 36134437 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 69281 69536 36134437
    (by decide) (by decide) weights317

private theorem weights318 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 69537 69792 = 38414517 := by
  decide +kernel

private theorem batch318 :
    (∑ n ∈ Finset.Icc 69537 69792, roundedTerm 10000000000 n) = 38414517 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 69537 69792 38414517
    (by decide) (by decide) weights318

private theorem weights319 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 69793 69861 = 9556542 := by
  decide +kernel

private theorem batch319 :
    (∑ n ∈ Finset.Icc 69793 69861, roundedTerm 10000000000 n) = 9556542 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 69793 69861 9556542
    (by decide) (by decide) weights319

set_option trace.profiler true in
private theorem weights320 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 69862 70117 = 36835716 := by
  decide +kernel

private theorem batch320 :
    (∑ n ∈ Finset.Icc 69862 70117, roundedTerm 10000000000 n) = 36835716 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 69862 70117 36835716
    (by decide) (by decide) weights320

private theorem weights321 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 70118 70373 = 35939257 := by
  decide +kernel

private theorem batch321 :
    (∑ n ∈ Finset.Icc 70118 70373, roundedTerm 10000000000 n) = 35939257 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 70118 70373 35939257
    (by decide) (by decide) weights321

private theorem weights322 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 70374 70629 = 35831719 := by
  decide +kernel

private theorem batch322 :
    (∑ n ∈ Finset.Icc 70374 70629, roundedTerm 10000000000 n) = 35831719 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 70374 70629 35831719
    (by decide) (by decide) weights322

private theorem weights323 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 70630 70885 = 36544640 := by
  decide +kernel

private theorem batch323 :
    (∑ n ∈ Finset.Icc 70630 70885, roundedTerm 10000000000 n) = 36544640 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 70630 70885 36544640
    (by decide) (by decide) weights323

private theorem weights324 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 70886 71141 = 36269793 := by
  decide +kernel

private theorem batch324 :
    (∑ n ∈ Finset.Icc 70886 71141, roundedTerm 10000000000 n) = 36269793 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 70886 71141 36269793
    (by decide) (by decide) weights324

private theorem weights325 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 71142 71397 = 35124141 := by
  decide +kernel

private theorem batch325 :
    (∑ n ∈ Finset.Icc 71142 71397, roundedTerm 10000000000 n) = 35124141 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 71142 71397 35124141
    (by decide) (by decide) weights325

private theorem weights326 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 71398 71653 = 36610432 := by
  decide +kernel

private theorem batch326 :
    (∑ n ∈ Finset.Icc 71398 71653, roundedTerm 10000000000 n) = 36610432 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 71398 71653 36610432
    (by decide) (by decide) weights326

private theorem weights327 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 71654 71909 = 36934002 := by
  decide +kernel

private theorem batch327 :
    (∑ n ∈ Finset.Icc 71654 71909, roundedTerm 10000000000 n) = 36934002 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 71654 71909 36934002
    (by decide) (by decide) weights327

private theorem weights328 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 71910 72165 = 34632516 := by
  decide +kernel

private theorem batch328 :
    (∑ n ∈ Finset.Icc 71910 72165, roundedTerm 10000000000 n) = 34632516 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 71910 72165 34632516
    (by decide) (by decide) weights328

private theorem weights329 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 72166 72421 = 35802355 := by
  decide +kernel

private theorem batch329 :
    (∑ n ∈ Finset.Icc 72166 72421, roundedTerm 10000000000 n) = 35802355 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 72166 72421 35802355
    (by decide) (by decide) weights329

private theorem weights330 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 72422 72677 = 34483080 := by
  decide +kernel

private theorem batch330 :
    (∑ n ∈ Finset.Icc 72422 72677, roundedTerm 10000000000 n) = 34483080 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 72422 72677 34483080
    (by decide) (by decide) weights330

private theorem weights331 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 72678 72933 = 35939899 := by
  decide +kernel

private theorem batch331 :
    (∑ n ∈ Finset.Icc 72678 72933, roundedTerm 10000000000 n) = 35939899 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 72678 72933 35939899
    (by decide) (by decide) weights331

private theorem weights332 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 72934 73189 = 33804211 := by
  decide +kernel

private theorem batch332 :
    (∑ n ∈ Finset.Icc 72934 73189, roundedTerm 10000000000 n) = 33804211 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 72934 73189 33804211
    (by decide) (by decide) weights332

private theorem weights333 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 73190 73445 = 35047788 := by
  decide +kernel

private theorem batch333 :
    (∑ n ∈ Finset.Icc 73190 73445, roundedTerm 10000000000 n) = 35047788 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 73190 73445 35047788
    (by decide) (by decide) weights333

private theorem weights334 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 73446 73701 = 34951410 := by
  decide +kernel

private theorem batch334 :
    (∑ n ∈ Finset.Icc 73446 73701, roundedTerm 10000000000 n) = 34951410 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 73446 73701 34951410
    (by decide) (by decide) weights334

private theorem weights335 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 73702 73957 = 34139579 := by
  decide +kernel

private theorem batch335 :
    (∑ n ∈ Finset.Icc 73702 73957, roundedTerm 10000000000 n) = 34139579 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 73702 73957 34139579
    (by decide) (by decide) weights335

private theorem weights336 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 73958 74213 = 34846601 := by
  decide +kernel

private theorem batch336 :
    (∑ n ∈ Finset.Icc 73958 74213, roundedTerm 10000000000 n) = 34846601 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 73958 74213 34846601
    (by decide) (by decide) weights336

private theorem weights337 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 74214 74469 = 33972736 := by
  decide +kernel

private theorem batch337 :
    (∑ n ∈ Finset.Icc 74214 74469, roundedTerm 10000000000 n) = 33972736 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 74214 74469 33972736
    (by decide) (by decide) weights337

private theorem weights338 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 74470 74725 = 34139810 := by
  decide +kernel

private theorem batch338 :
    (∑ n ∈ Finset.Icc 74470 74725, roundedTerm 10000000000 n) = 34139810 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 74470 74725 34139810
    (by decide) (by decide) weights338

private theorem weights339 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 74726 74981 = 33590839 := by
  decide +kernel

private theorem batch339 :
    (∑ n ∈ Finset.Icc 74726 74981, roundedTerm 10000000000 n) = 33590839 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 74726 74981 33590839
    (by decide) (by decide) weights339

private theorem weights340 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 74982 75237 = 34940670 := by
  decide +kernel

private theorem batch340 :
    (∑ n ∈ Finset.Icc 74982 75237, roundedTerm 10000000000 n) = 34940670 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 74982 75237 34940670
    (by decide) (by decide) weights340

private theorem weights341 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 75238 75493 = 34190570 := by
  decide +kernel

private theorem batch341 :
    (∑ n ∈ Finset.Icc 75238 75493, roundedTerm 10000000000 n) = 34190570 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 75238 75493 34190570
    (by decide) (by decide) weights341

private theorem weights342 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 75494 75749 = 33527821 := by
  decide +kernel

private theorem batch342 :
    (∑ n ∈ Finset.Icc 75494 75749, roundedTerm 10000000000 n) = 33527821 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 75494 75749 33527821
    (by decide) (by decide) weights342

private theorem weights343 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 75750 76005 = 33271456 := by
  decide +kernel

private theorem batch343 :
    (∑ n ∈ Finset.Icc 75750 76005, roundedTerm 10000000000 n) = 33271456 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 75750 76005 33271456
    (by decide) (by decide) weights343

private theorem weights344 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 76006 76261 = 34223745 := by
  decide +kernel

private theorem batch344 :
    (∑ n ∈ Finset.Icc 76006 76261, roundedTerm 10000000000 n) = 34223745 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 76006 76261 34223745
    (by decide) (by decide) weights344

private theorem weights345 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 76262 76517 = 34836821 := by
  decide +kernel

private theorem batch345 :
    (∑ n ∈ Finset.Icc 76262 76517, roundedTerm 10000000000 n) = 34836821 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 76262 76517 34836821
    (by decide) (by decide) weights345

private theorem weights346 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 76518 76773 = 31701456 := by
  decide +kernel

private theorem batch346 :
    (∑ n ∈ Finset.Icc 76518 76773, roundedTerm 10000000000 n) = 31701456 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 76518 76773 31701456
    (by decide) (by decide) weights346

private theorem weights347 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 76774 77029 = 33543245 := by
  decide +kernel

private theorem batch347 :
    (∑ n ∈ Finset.Icc 76774 77029, roundedTerm 10000000000 n) = 33543245 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 76774 77029 33543245
    (by decide) (by decide) weights347

private theorem weights348 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 77030 77285 = 33138513 := by
  decide +kernel

private theorem batch348 :
    (∑ n ∈ Finset.Icc 77030 77285, roundedTerm 10000000000 n) = 33138513 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 77030 77285 33138513
    (by decide) (by decide) weights348

private theorem weights349 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 77286 77541 = 33148204 := by
  decide +kernel

private theorem batch349 :
    (∑ n ∈ Finset.Icc 77286 77541, roundedTerm 10000000000 n) = 33148204 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 77286 77541 33148204
    (by decide) (by decide) weights349

private theorem weights350 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 77542 77797 = 32308150 := by
  decide +kernel

private theorem batch350 :
    (∑ n ∈ Finset.Icc 77542 77797, roundedTerm 10000000000 n) = 32308150 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 77542 77797 32308150
    (by decide) (by decide) weights350

private theorem weights351 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 77798 78053 = 33195150 := by
  decide +kernel

private theorem batch351 :
    (∑ n ∈ Finset.Icc 77798 78053, roundedTerm 10000000000 n) = 33195150 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 77798 78053 33195150
    (by decide) (by decide) weights351

set_option trace.profiler true in
private theorem weights352 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 78054 78309 = 32223214 := by
  decide +kernel

private theorem batch352 :
    (∑ n ∈ Finset.Icc 78054 78309, roundedTerm 10000000000 n) = 32223214 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 78054 78309 32223214
    (by decide) (by decide) weights352

private theorem weights353 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 78310 78565 = 33459542 := by
  decide +kernel

private theorem batch353 :
    (∑ n ∈ Finset.Icc 78310 78565, roundedTerm 10000000000 n) = 33459542 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 78310 78565 33459542
    (by decide) (by decide) weights353

private theorem weights354 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 78566 78821 = 32575459 := by
  decide +kernel

private theorem batch354 :
    (∑ n ∈ Finset.Icc 78566 78821, roundedTerm 10000000000 n) = 32575459 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 78566 78821 32575459
    (by decide) (by decide) weights354

private theorem weights355 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 78822 79077 = 31763807 := by
  decide +kernel

private theorem batch355 :
    (∑ n ∈ Finset.Icc 78822 79077, roundedTerm 10000000000 n) = 31763807 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 78822 79077 31763807
    (by decide) (by decide) weights355

private theorem weights356 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 79078 79333 = 31323817 := by
  decide +kernel

private theorem batch356 :
    (∑ n ∈ Finset.Icc 79078 79333, roundedTerm 10000000000 n) = 31323817 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 79078 79333 31323817
    (by decide) (by decide) weights356

private theorem weights357 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 79334 79589 = 32326351 := by
  decide +kernel

private theorem batch357 :
    (∑ n ∈ Finset.Icc 79334 79589, roundedTerm 10000000000 n) = 32326351 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 79334 79589 32326351
    (by decide) (by decide) weights357

private theorem weights358 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 79590 79845 = 32880226 := by
  decide +kernel

private theorem batch358 :
    (∑ n ∈ Finset.Icc 79590 79845, roundedTerm 10000000000 n) = 32880226 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 79590 79845 32880226
    (by decide) (by decide) weights358

private theorem weights359 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 79846 80101 = 31444808 := by
  decide +kernel

private theorem batch359 :
    (∑ n ∈ Finset.Icc 79846 80101, roundedTerm 10000000000 n) = 31444808 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 79846 80101 31444808
    (by decide) (by decide) weights359

private theorem weights360 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 80102 80257 = 18416784 := by
  decide +kernel

private theorem batch360 :
    (∑ n ∈ Finset.Icc 80102 80257, roundedTerm 10000000000 n) = 18416784 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 80102 80257 18416784
    (by decide) (by decide) weights360

private theorem all_semantic_batches :
    ∀ g ∈ batchGroups, ∀ b ∈ g.batches,
      (∑ n ∈ Finset.Icc b.lo b.hi, roundedTerm 10000000000 n) = b.value := by
  exact List.forall_iff_forall_mem.mp
    ⟨
      List.forall_iff_forall_mem.mp batch000,
      List.forall_iff_forall_mem.mp batch001,
      List.forall_iff_forall_mem.mp batch002,
      List.forall_iff_forall_mem.mp batch003,
      List.forall_iff_forall_mem.mp batch004,
      List.forall_iff_forall_mem.mp batch005,
      List.forall_iff_forall_mem.mp batch006,
      List.forall_iff_forall_mem.mp batch007,
      List.forall_iff_forall_mem.mp batch008,
      List.forall_iff_forall_mem.mp batch009,
      List.forall_iff_forall_mem.mp batch010,
      List.forall_iff_forall_mem.mp batch011,
      List.forall_iff_forall_mem.mp batch012,
      List.forall_iff_forall_mem.mp batch013,
      List.forall_iff_forall_mem.mp batch014,
      List.forall_iff_forall_mem.mp batch015,
      List.forall_iff_forall_mem.mp batch016,
      List.forall_iff_forall_mem.mp batch017,
      List.forall_iff_forall_mem.mp batch018,
      List.forall_iff_forall_mem.mp batch019,
      List.forall_iff_forall_mem.mp batch020,
      List.forall_iff_forall_mem.mp batch021,
      List.forall_iff_forall_mem.mp batch022,
      List.forall_iff_forall_mem.mp batch023,
      List.forall_iff_forall_mem.mp batch024,
      List.forall_iff_forall_mem.mp batch025,
      List.forall_iff_forall_mem.mp batch026,
      List.forall_iff_forall_mem.mp batch027,
      List.forall_iff_forall_mem.mp batch028,
      List.forall_iff_forall_mem.mp batch029,
      List.forall_iff_forall_mem.mp batch030,
      List.forall_iff_forall_mem.mp batch031,
      List.forall_iff_forall_mem.mp batch032,
      List.forall_iff_forall_mem.mp batch033,
      List.forall_iff_forall_mem.mp batch034,
      List.forall_iff_forall_mem.mp batch035,
      List.forall_iff_forall_mem.mp batch036,
      List.forall_iff_forall_mem.mp batch037,
      List.forall_iff_forall_mem.mp batch038,
      List.forall_iff_forall_mem.mp batch039,
      List.forall_iff_forall_mem.mp batch040,
      List.forall_iff_forall_mem.mp batch041,
      List.forall_iff_forall_mem.mp ⟨batch042, batch043⟩,
      List.forall_iff_forall_mem.mp ⟨batch044, batch045⟩,
      List.forall_iff_forall_mem.mp ⟨batch046, batch047⟩,
      List.forall_iff_forall_mem.mp ⟨batch048, batch049⟩,
      List.forall_iff_forall_mem.mp ⟨batch050, batch051⟩,
      List.forall_iff_forall_mem.mp ⟨batch052, batch053, batch054⟩,
      List.forall_iff_forall_mem.mp ⟨batch055, batch056, batch057⟩,
      List.forall_iff_forall_mem.mp ⟨batch058, batch059, batch060⟩,
      List.forall_iff_forall_mem.mp ⟨batch061, batch062, batch063, batch064⟩,
      List.forall_iff_forall_mem.mp ⟨batch065, batch066, batch067, batch068⟩,
      List.forall_iff_forall_mem.mp ⟨batch069, batch070, batch071, batch072, batch073⟩,
      List.forall_iff_forall_mem.mp ⟨batch074, batch075, batch076, batch077, batch078, batch079⟩,
      List.forall_iff_forall_mem.mp ⟨batch080, batch081, batch082, batch083, batch084, batch085⟩,
      List.forall_iff_forall_mem.mp ⟨batch086, batch087, batch088, batch089, batch090, batch091, batch092⟩,
      List.forall_iff_forall_mem.mp ⟨batch093, batch094, batch095, batch096, batch097, batch098, batch099, batch100⟩,
      List.forall_iff_forall_mem.mp ⟨batch101, batch102, batch103, batch104, batch105, batch106, batch107, batch108, batch109⟩,
      List.forall_iff_forall_mem.mp ⟨batch110, batch111, batch112, batch113, batch114, batch115, batch116, batch117, batch118, batch119, batch120⟩,
      List.forall_iff_forall_mem.mp ⟨batch121, batch122, batch123, batch124, batch125, batch126, batch127, batch128, batch129, batch130, batch131, batch132⟩,
      List.forall_iff_forall_mem.mp ⟨batch133, batch134, batch135, batch136, batch137, batch138, batch139, batch140, batch141, batch142, batch143, batch144, batch145, batch146⟩,
      List.forall_iff_forall_mem.mp ⟨batch147, batch148, batch149, batch150, batch151, batch152, batch153, batch154, batch155, batch156, batch157, batch158, batch159, batch160, batch161, batch162⟩,
      List.forall_iff_forall_mem.mp ⟨batch163, batch164, batch165, batch166, batch167, batch168, batch169, batch170, batch171, batch172, batch173, batch174, batch175, batch176, batch177, batch178, batch179, batch180⟩,
      List.forall_iff_forall_mem.mp ⟨batch181, batch182, batch183, batch184, batch185, batch186, batch187, batch188, batch189, batch190, batch191, batch192, batch193, batch194, batch195, batch196, batch197, batch198, batch199, batch200, batch201⟩,
      List.forall_iff_forall_mem.mp ⟨batch202, batch203, batch204, batch205, batch206, batch207, batch208, batch209, batch210, batch211, batch212, batch213, batch214, batch215, batch216, batch217, batch218, batch219, batch220, batch221, batch222, batch223, batch224, batch225⟩,
      List.forall_iff_forall_mem.mp ⟨batch226, batch227, batch228, batch229, batch230, batch231, batch232, batch233, batch234, batch235, batch236, batch237, batch238, batch239, batch240, batch241, batch242, batch243, batch244, batch245, batch246, batch247, batch248, batch249, batch250, batch251, batch252⟩,
      List.forall_iff_forall_mem.mp ⟨batch253, batch254, batch255, batch256, batch257, batch258, batch259, batch260, batch261, batch262, batch263, batch264, batch265, batch266, batch267, batch268, batch269, batch270, batch271, batch272, batch273, batch274, batch275, batch276, batch277, batch278, batch279, batch280, batch281, batch282, batch283⟩,
      List.forall_iff_forall_mem.mp ⟨batch284, batch285, batch286, batch287, batch288, batch289, batch290, batch291, batch292, batch293, batch294, batch295, batch296, batch297, batch298, batch299, batch300, batch301, batch302, batch303, batch304, batch305, batch306, batch307, batch308, batch309, batch310, batch311, batch312, batch313, batch314, batch315, batch316, batch317, batch318, batch319⟩,
      List.forall_iff_forall_mem.mp ⟨batch320, batch321, batch322, batch323, batch324, batch325, batch326, batch327, batch328, batch329, batch330, batch331, batch332, batch333, batch334, batch335, batch336, batch337, batch338, batch339, batch340, batch341, batch342, batch343, batch344, batch345, batch346, batch347, batch348, batch349, batch350, batch351, batch352, batch353, batch354, batch355, batch356, batch357, batch358, batch359, batch360⟩
    ⟩

/-- Exact prefix totals on the selected public endpoint range. -/
private theorem endpoint_prefixes_range  :
    ∀ e ∈ RamareFiniteBounds.logEndpoints, e.hi ≤ 80257 →
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper := by
  have hall := batchGroupsCheck_sound (roundedTerm 10000000000) batchGroups 1 0
    (by decide) (by simp) batchGroups_checked all_semantic_batches
  intro e he hrange
  have hm : e ∈ batchGroups.map EndpointBatchGroup.endpoint := by
    rw [batchGroups_endpoints]
    simpa only [List.mem_filter, decide_eq_true_eq] using (And.intro he hrange)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
  exact hall g hg

end RamareFiniteBoundsArithmetic

theorem solution  :
    ∀ e ∈ RamareFiniteBounds.logEndpoints, e.hi ≤ 80257 →
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper :=
  RamareFiniteBoundsArithmetic.endpoint_prefixes_range

#print axioms solution
