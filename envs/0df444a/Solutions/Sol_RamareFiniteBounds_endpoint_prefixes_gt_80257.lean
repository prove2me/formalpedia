-- Prove2me | solution 1 for RamareFiniteBounds.endpoint_prefixes_gt_80257
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:13:09.390002+00:00
-- url     : https://prove2.me/submissions/0c95e6da-0dd5-4c8d-9308-818889f7a1f5

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
    ⟨⟨80258, 92156, 16, 127638869874⟩, [
      ⟨80258, 80513, 32646585⟩,
      ⟨80514, 80769, 32674447⟩,
      ⟨80770, 81025, 32070585⟩,
      ⟨81026, 81281, 31306174⟩,
      ⟨81282, 81537, 31663669⟩,
      ⟨81538, 81793, 31003488⟩,
      ⟨81794, 82049, 31201592⟩,
      ⟨82050, 82305, 31793563⟩,
      ⟨82306, 82561, 31739411⟩,
      ⟨82562, 82817, 30665354⟩,
      ⟨82818, 83073, 30320979⟩,
      ⟨83074, 83329, 31557658⟩,
      ⟨83330, 83585, 29981127⟩,
      ⟨83586, 83841, 30846001⟩,
      ⟨83842, 84097, 30674064⟩,
      ⟨84098, 84353, 30083557⟩,
      ⟨84354, 84609, 30805325⟩,
      ⟨84610, 84865, 30226722⟩,
      ⟨84866, 85121, 30603240⟩,
      ⟨85122, 85377, 29555094⟩,
      ⟨85378, 85633, 30068894⟩,
      ⟨85634, 85889, 29544243⟩,
      ⟨85890, 86145, 30141539⟩,
      ⟨86146, 86401, 28821642⟩,
      ⟨86402, 86657, 30015001⟩,
      ⟨86658, 86913, 30024537⟩,
      ⟨86914, 87169, 29426606⟩,
      ⟨87170, 87425, 29109279⟩,
      ⟨87426, 87681, 28978662⟩,
      ⟨87682, 87937, 29473183⟩,
      ⟨87938, 88193, 29330431⟩,
      ⟨88194, 88449, 29297162⟩,
      ⟨88450, 88705, 29456433⟩,
      ⟨88706, 88961, 28657501⟩,
      ⟨88962, 89217, 29011908⟩,
      ⟨89218, 89473, 28821687⟩,
      ⟨89474, 89729, 28523584⟩,
      ⟨89730, 89985, 27968264⟩,
      ⟨89986, 90241, 29038890⟩,
      ⟨90242, 90497, 27614466⟩,
      ⟨90498, 90753, 28297018⟩,
      ⟨90754, 91009, 28844553⟩,
      ⟨91010, 91265, 28505046⟩,
      ⟨91266, 91521, 28657058⟩,
      ⟨91522, 91777, 27119398⟩,
      ⟨91778, 92033, 28316459⟩,
      ⟨92034, 92156, 12699937⟩
    ]⟩,
    ⟨⟨92157, 105818, 16, 129021341399⟩, [
      ⟨92157, 92412, 28167730⟩,
      ⟨92413, 92668, 27751645⟩,
      ⟨92669, 92924, 27500528⟩,
      ⟨92925, 93180, 27373824⟩,
      ⟨93181, 93436, 27729701⟩,
      ⟨93437, 93692, 26520394⟩,
      ⟨93693, 93948, 28037909⟩,
      ⟨93949, 94204, 26851950⟩,
      ⟨94205, 94460, 27511907⟩,
      ⟨94461, 94716, 27020049⟩,
      ⟨94717, 94972, 27467555⟩,
      ⟨94973, 95228, 26702468⟩,
      ⟨95229, 95484, 26633437⟩,
      ⟨95485, 95740, 26965982⟩,
      ⟨95741, 95996, 26013057⟩,
      ⟨95997, 96252, 26806151⟩,
      ⟨96253, 96508, 25846453⟩,
      ⟨96509, 96764, 26193590⟩,
      ⟨96765, 97020, 26686035⟩,
      ⟨97021, 97276, 26111540⟩,
      ⟨97277, 97532, 26372721⟩,
      ⟨97533, 97788, 26486322⟩,
      ⟨97789, 98044, 26354640⟩,
      ⟨98045, 98300, 25680176⟩,
      ⟨98301, 98556, 25416205⟩,
      ⟨98557, 98812, 26650764⟩,
      ⟨98813, 99068, 25482895⟩,
      ⟨99069, 99324, 26163624⟩,
      ⟨99325, 99580, 25902987⟩,
      ⟨99581, 99836, 26298198⟩,
      ⟨99837, 100092, 24853972⟩,
      ⟨100093, 100348, 26386121⟩,
      ⟨100349, 100604, 25261429⟩,
      ⟨100605, 100860, 25639220⟩,
      ⟨100861, 101116, 24966987⟩,
      ⟨101117, 101372, 25954015⟩,
      ⟨101373, 101628, 25265617⟩,
      ⟨101629, 101884, 24693883⟩,
      ⟨101885, 102140, 25735221⟩,
      ⟨102141, 102396, 25320394⟩,
      ⟨102397, 102652, 24072012⟩,
      ⟨102653, 102908, 25248226⟩,
      ⟨102909, 103164, 24289907⟩,
      ⟨103165, 103420, 24555551⟩,
      ⟨103421, 103676, 24653294⟩,
      ⟨103677, 103932, 24786431⟩,
      ⟨103933, 104188, 25036403⟩,
      ⟨104189, 104444, 23799950⟩,
      ⟨104445, 104700, 24453394⟩,
      ⟨104701, 104956, 24645315⟩,
      ⟨104957, 105212, 24471930⟩,
      ⟨105213, 105468, 24309813⟩,
      ⟨105469, 105724, 24645138⟩,
      ⟨105725, 105818, 8726865⟩
    ]⟩,
    ⟨⟨105819, 121525, 16, 130403721186⟩, [
      ⟨105819, 106074, 24264360⟩,
      ⟨106075, 106330, 23677669⟩,
      ⟨106331, 106586, 24511342⟩,
      ⟨106587, 106842, 24489564⟩,
      ⟨106843, 107098, 23726120⟩,
      ⟨107099, 107354, 23393381⟩,
      ⟨107355, 107610, 24516992⟩,
      ⟨107611, 107866, 23730647⟩,
      ⟨107867, 108122, 23783417⟩,
      ⟨108123, 108378, 23264892⟩,
      ⟨108379, 108634, 23935356⟩,
      ⟨108635, 108890, 23574876⟩,
      ⟨108891, 109146, 23358256⟩,
      ⟨109147, 109402, 23253800⟩,
      ⟨109403, 109658, 22834543⟩,
      ⟨109659, 109914, 23769409⟩,
      ⟨109915, 110170, 23268033⟩,
      ⟨110171, 110426, 23827366⟩,
      ⟨110427, 110682, 22655042⟩,
      ⟨110683, 110938, 23101632⟩,
      ⟨110939, 111194, 22799175⟩,
      ⟨111195, 111450, 22762056⟩,
      ⟨111451, 111706, 22807337⟩,
      ⟨111707, 111962, 22774261⟩,
      ⟨111963, 112218, 23469481⟩,
      ⟨112219, 112474, 22756842⟩,
      ⟨112475, 112730, 21838205⟩,
      ⟨112731, 112986, 22943074⟩,
      ⟨112987, 113242, 22020258⟩,
      ⟨113243, 113498, 22479899⟩,
      ⟨113499, 113754, 22463375⟩,
      ⟨113755, 114010, 22882940⟩,
      ⟨114011, 114266, 22688137⟩,
      ⟨114267, 114522, 22407951⟩,
      ⟨114523, 114778, 22160781⟩,
      ⟨114779, 115034, 22252553⟩,
      ⟨115035, 115290, 22149642⟩,
      ⟨115291, 115546, 22338518⟩,
      ⟨115547, 115802, 22588466⟩,
      ⟨115803, 116058, 21326806⟩,
      ⟨116059, 116314, 21760695⟩,
      ⟨116315, 116570, 22232158⟩,
      ⟨116571, 116826, 21779737⟩,
      ⟨116827, 117082, 21731261⟩,
      ⟨117083, 117338, 21627456⟩,
      ⟨117339, 117594, 21660490⟩,
      ⟨117595, 117850, 21521324⟩,
      ⟨117851, 118106, 21200695⟩,
      ⟨118107, 118362, 21518278⟩,
      ⟨118363, 118618, 21987118⟩,
      ⟨118619, 118874, 21030655⟩,
      ⟨118875, 119130, 21921269⟩,
      ⟨119131, 119386, 21255277⟩,
      ⟨119387, 119642, 21568303⟩,
      ⟨119643, 119898, 21300514⟩,
      ⟨119899, 120154, 21671286⟩,
      ⟨120155, 120410, 21534141⟩,
      ⟨120411, 120666, 20812537⟩,
      ⟨120667, 120922, 21457000⟩,
      ⟨120923, 121178, 21267184⟩,
      ⟨121179, 121434, 21394464⟩,
      ⟨121435, 121525, 7301491⟩
    ]⟩,
    ⟨⟨121526, 139545, 16, 131787790876⟩, [
      ⟨121526, 121781, 20702707⟩,
      ⟨121782, 122037, 20547326⟩,
      ⟨122038, 122293, 20948369⟩,
      ⟨122294, 122549, 21240695⟩,
      ⟨122550, 122805, 20695952⟩,
      ⟨122806, 123061, 21375458⟩,
      ⟨123062, 123317, 20851872⟩,
      ⟨123318, 123573, 20572195⟩,
      ⟨123574, 123829, 20939770⟩,
      ⟨123830, 124085, 20793419⟩,
      ⟨124086, 124341, 20911713⟩,
      ⟨124342, 124597, 20630053⟩,
      ⟨124598, 124853, 20949156⟩,
      ⟨124854, 125109, 20815339⟩,
      ⟨125110, 125365, 20383674⟩,
      ⟨125366, 125621, 20272687⟩,
      ⟨125622, 125877, 20618015⟩,
      ⟨125878, 126133, 19636991⟩,
      ⟨126134, 126389, 20600405⟩,
      ⟨126390, 126645, 20581061⟩,
      ⟨126646, 126901, 20379489⟩,
      ⟨126902, 127157, 20175637⟩,
      ⟨127158, 127413, 20764634⟩,
      ⟨127414, 127669, 19878597⟩,
      ⟨127670, 127925, 19836827⟩,
      ⟨127926, 128181, 19470928⟩,
      ⟨128182, 128437, 20756881⟩,
      ⟨128438, 128693, 19845308⟩,
      ⟨128694, 128949, 19481098⟩,
      ⟨128950, 129205, 20138201⟩,
      ⟨129206, 129461, 19455114⟩,
      ⟨129462, 129717, 19957463⟩,
      ⟨129718, 129973, 20042971⟩,
      ⟨129974, 130229, 19903829⟩,
      ⟨130230, 130485, 19090072⟩,
      ⟨130486, 130741, 19743528⟩,
      ⟨130742, 130997, 19704644⟩,
      ⟨130998, 131253, 19404092⟩,
      ⟨131254, 131509, 19281796⟩,
      ⟨131510, 131765, 19365740⟩,
      ⟨131766, 132021, 19771314⟩,
      ⟨132022, 132277, 18796649⟩,
      ⟨132278, 132533, 19479508⟩,
      ⟨132534, 132789, 19226335⟩,
      ⟨132790, 133045, 19023170⟩,
      ⟨133046, 133301, 19306664⟩,
      ⟨133302, 133557, 19056353⟩,
      ⟨133558, 133813, 19068765⟩,
      ⟨133814, 134069, 19096244⟩,
      ⟨134070, 134325, 19186235⟩,
      ⟨134326, 134581, 19066899⟩,
      ⟨134582, 134837, 18933434⟩,
      ⟨134838, 135093, 18355200⟩,
      ⟨135094, 135349, 19249998⟩,
      ⟨135350, 135605, 18910555⟩,
      ⟨135606, 135861, 18701596⟩,
      ⟨135862, 136117, 19277326⟩,
      ⟨136118, 136373, 18917027⟩,
      ⟨136374, 136629, 18942952⟩,
      ⟨136630, 136885, 18290094⟩,
      ⟨136886, 137141, 18621085⟩,
      ⟨137142, 137397, 18837059⟩,
      ⟨137398, 137653, 18504623⟩,
      ⟨137654, 137909, 18150648⟩,
      ⟨137910, 138165, 19081338⟩,
      ⟨138166, 138421, 18752260⟩,
      ⟨138422, 138677, 18113182⟩,
      ⟨138678, 138933, 18660965⟩,
      ⟨138934, 139189, 18370190⟩,
      ⟨139190, 139445, 18473716⟩,
      ⟨139446, 139545, 7104600⟩
    ]⟩,
    ⟨⟨139546, 142300, 17, 131983841862⟩, [
      ⟨139546, 139801, 17908123⟩,
      ⟨139802, 140057, 18835235⟩,
      ⟨140058, 140313, 18067301⟩,
      ⟨140314, 140569, 18269450⟩,
      ⟨140570, 140825, 18066321⟩,
      ⟨140826, 141081, 18419591⟩,
      ⟨141082, 141337, 18026282⟩,
      ⟨141338, 141593, 18287451⟩,
      ⟨141594, 141849, 18480821⟩,
      ⟨141850, 142105, 18211895⟩,
      ⟨142106, 142300, 13478516⟩
    ]⟩
  ]

/-- Exact filtered public endpoints; all four record fields are preserved. -/
private theorem batchGroups_endpoints :
    batchGroups.map EndpointBatchGroup.endpoint =
      logEndpoints.filter (fun e => decide (80257 < e.hi)) := by
  decide +kernel

/-- Contiguous interval and integer-total checks only. -/
private theorem batchGroups_checked : batchGroupsCheck 80258 126251687858 batchGroups = true := by
  decide +kernel

private theorem weights361 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 80258 80513 = 32646585 := by
  decide +kernel

private theorem batch361 :
    (∑ n ∈ Finset.Icc 80258 80513, roundedTerm 10000000000 n) = 32646585 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 80258 80513 32646585
    (by decide) (by decide) weights361

private theorem weights362 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 80514 80769 = 32674447 := by
  decide +kernel

private theorem batch362 :
    (∑ n ∈ Finset.Icc 80514 80769, roundedTerm 10000000000 n) = 32674447 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 80514 80769 32674447
    (by decide) (by decide) weights362

private theorem weights363 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 80770 81025 = 32070585 := by
  decide +kernel

private theorem batch363 :
    (∑ n ∈ Finset.Icc 80770 81025, roundedTerm 10000000000 n) = 32070585 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 80770 81025 32070585
    (by decide) (by decide) weights363

private theorem weights364 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 81026 81281 = 31306174 := by
  decide +kernel

private theorem batch364 :
    (∑ n ∈ Finset.Icc 81026 81281, roundedTerm 10000000000 n) = 31306174 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 81026 81281 31306174
    (by decide) (by decide) weights364

private theorem weights365 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 81282 81537 = 31663669 := by
  decide +kernel

private theorem batch365 :
    (∑ n ∈ Finset.Icc 81282 81537, roundedTerm 10000000000 n) = 31663669 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 81282 81537 31663669
    (by decide) (by decide) weights365

private theorem weights366 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 81538 81793 = 31003488 := by
  decide +kernel

private theorem batch366 :
    (∑ n ∈ Finset.Icc 81538 81793, roundedTerm 10000000000 n) = 31003488 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 81538 81793 31003488
    (by decide) (by decide) weights366

private theorem weights367 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 81794 82049 = 31201592 := by
  decide +kernel

private theorem batch367 :
    (∑ n ∈ Finset.Icc 81794 82049, roundedTerm 10000000000 n) = 31201592 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 81794 82049 31201592
    (by decide) (by decide) weights367

private theorem weights368 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 82050 82305 = 31793563 := by
  decide +kernel

private theorem batch368 :
    (∑ n ∈ Finset.Icc 82050 82305, roundedTerm 10000000000 n) = 31793563 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 82050 82305 31793563
    (by decide) (by decide) weights368

private theorem weights369 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 82306 82561 = 31739411 := by
  decide +kernel

private theorem batch369 :
    (∑ n ∈ Finset.Icc 82306 82561, roundedTerm 10000000000 n) = 31739411 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 82306 82561 31739411
    (by decide) (by decide) weights369

private theorem weights370 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 82562 82817 = 30665354 := by
  decide +kernel

private theorem batch370 :
    (∑ n ∈ Finset.Icc 82562 82817, roundedTerm 10000000000 n) = 30665354 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 82562 82817 30665354
    (by decide) (by decide) weights370

private theorem weights371 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 82818 83073 = 30320979 := by
  decide +kernel

private theorem batch371 :
    (∑ n ∈ Finset.Icc 82818 83073, roundedTerm 10000000000 n) = 30320979 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 82818 83073 30320979
    (by decide) (by decide) weights371

private theorem weights372 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 83074 83329 = 31557658 := by
  decide +kernel

private theorem batch372 :
    (∑ n ∈ Finset.Icc 83074 83329, roundedTerm 10000000000 n) = 31557658 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 83074 83329 31557658
    (by decide) (by decide) weights372

private theorem weights373 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 83330 83585 = 29981127 := by
  decide +kernel

private theorem batch373 :
    (∑ n ∈ Finset.Icc 83330 83585, roundedTerm 10000000000 n) = 29981127 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 83330 83585 29981127
    (by decide) (by decide) weights373

private theorem weights374 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 83586 83841 = 30846001 := by
  decide +kernel

private theorem batch374 :
    (∑ n ∈ Finset.Icc 83586 83841, roundedTerm 10000000000 n) = 30846001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 83586 83841 30846001
    (by decide) (by decide) weights374

private theorem weights375 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 83842 84097 = 30674064 := by
  decide +kernel

private theorem batch375 :
    (∑ n ∈ Finset.Icc 83842 84097, roundedTerm 10000000000 n) = 30674064 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 83842 84097 30674064
    (by decide) (by decide) weights375

private theorem weights376 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 84098 84353 = 30083557 := by
  decide +kernel

private theorem batch376 :
    (∑ n ∈ Finset.Icc 84098 84353, roundedTerm 10000000000 n) = 30083557 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 84098 84353 30083557
    (by decide) (by decide) weights376

private theorem weights377 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 84354 84609 = 30805325 := by
  decide +kernel

private theorem batch377 :
    (∑ n ∈ Finset.Icc 84354 84609, roundedTerm 10000000000 n) = 30805325 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 84354 84609 30805325
    (by decide) (by decide) weights377

private theorem weights378 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 84610 84865 = 30226722 := by
  decide +kernel

private theorem batch378 :
    (∑ n ∈ Finset.Icc 84610 84865, roundedTerm 10000000000 n) = 30226722 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 84610 84865 30226722
    (by decide) (by decide) weights378

private theorem weights379 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 84866 85121 = 30603240 := by
  decide +kernel

private theorem batch379 :
    (∑ n ∈ Finset.Icc 84866 85121, roundedTerm 10000000000 n) = 30603240 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 84866 85121 30603240
    (by decide) (by decide) weights379

private theorem weights380 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 85122 85377 = 29555094 := by
  decide +kernel

private theorem batch380 :
    (∑ n ∈ Finset.Icc 85122 85377, roundedTerm 10000000000 n) = 29555094 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 85122 85377 29555094
    (by decide) (by decide) weights380

private theorem weights381 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 85378 85633 = 30068894 := by
  decide +kernel

private theorem batch381 :
    (∑ n ∈ Finset.Icc 85378 85633, roundedTerm 10000000000 n) = 30068894 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 85378 85633 30068894
    (by decide) (by decide) weights381

private theorem weights382 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 85634 85889 = 29544243 := by
  decide +kernel

private theorem batch382 :
    (∑ n ∈ Finset.Icc 85634 85889, roundedTerm 10000000000 n) = 29544243 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 85634 85889 29544243
    (by decide) (by decide) weights382

private theorem weights383 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 85890 86145 = 30141539 := by
  decide +kernel

private theorem batch383 :
    (∑ n ∈ Finset.Icc 85890 86145, roundedTerm 10000000000 n) = 30141539 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 85890 86145 30141539
    (by decide) (by decide) weights383

set_option trace.profiler true in
private theorem weights384 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 86146 86401 = 28821642 := by
  decide +kernel

private theorem batch384 :
    (∑ n ∈ Finset.Icc 86146 86401, roundedTerm 10000000000 n) = 28821642 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 86146 86401 28821642
    (by decide) (by decide) weights384

private theorem weights385 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 86402 86657 = 30015001 := by
  decide +kernel

private theorem batch385 :
    (∑ n ∈ Finset.Icc 86402 86657, roundedTerm 10000000000 n) = 30015001 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 86402 86657 30015001
    (by decide) (by decide) weights385

private theorem weights386 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 86658 86913 = 30024537 := by
  decide +kernel

private theorem batch386 :
    (∑ n ∈ Finset.Icc 86658 86913, roundedTerm 10000000000 n) = 30024537 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 86658 86913 30024537
    (by decide) (by decide) weights386

private theorem weights387 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 86914 87169 = 29426606 := by
  decide +kernel

private theorem batch387 :
    (∑ n ∈ Finset.Icc 86914 87169, roundedTerm 10000000000 n) = 29426606 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 86914 87169 29426606
    (by decide) (by decide) weights387

private theorem weights388 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 87170 87425 = 29109279 := by
  decide +kernel

private theorem batch388 :
    (∑ n ∈ Finset.Icc 87170 87425, roundedTerm 10000000000 n) = 29109279 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 87170 87425 29109279
    (by decide) (by decide) weights388

private theorem weights389 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 87426 87681 = 28978662 := by
  decide +kernel

private theorem batch389 :
    (∑ n ∈ Finset.Icc 87426 87681, roundedTerm 10000000000 n) = 28978662 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 87426 87681 28978662
    (by decide) (by decide) weights389

private theorem weights390 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 87682 87937 = 29473183 := by
  decide +kernel

private theorem batch390 :
    (∑ n ∈ Finset.Icc 87682 87937, roundedTerm 10000000000 n) = 29473183 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 87682 87937 29473183
    (by decide) (by decide) weights390

private theorem weights391 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 87938 88193 = 29330431 := by
  decide +kernel

private theorem batch391 :
    (∑ n ∈ Finset.Icc 87938 88193, roundedTerm 10000000000 n) = 29330431 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 87938 88193 29330431
    (by decide) (by decide) weights391

private theorem weights392 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 88194 88449 = 29297162 := by
  decide +kernel

private theorem batch392 :
    (∑ n ∈ Finset.Icc 88194 88449, roundedTerm 10000000000 n) = 29297162 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 88194 88449 29297162
    (by decide) (by decide) weights392

private theorem weights393 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 88450 88705 = 29456433 := by
  decide +kernel

private theorem batch393 :
    (∑ n ∈ Finset.Icc 88450 88705, roundedTerm 10000000000 n) = 29456433 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 88450 88705 29456433
    (by decide) (by decide) weights393

private theorem weights394 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 88706 88961 = 28657501 := by
  decide +kernel

private theorem batch394 :
    (∑ n ∈ Finset.Icc 88706 88961, roundedTerm 10000000000 n) = 28657501 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 88706 88961 28657501
    (by decide) (by decide) weights394

private theorem weights395 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 88962 89217 = 29011908 := by
  decide +kernel

private theorem batch395 :
    (∑ n ∈ Finset.Icc 88962 89217, roundedTerm 10000000000 n) = 29011908 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 88962 89217 29011908
    (by decide) (by decide) weights395

private theorem weights396 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 89218 89473 = 28821687 := by
  decide +kernel

private theorem batch396 :
    (∑ n ∈ Finset.Icc 89218 89473, roundedTerm 10000000000 n) = 28821687 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 89218 89473 28821687
    (by decide) (by decide) weights396

private theorem weights397 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 89474 89729 = 28523584 := by
  decide +kernel

private theorem batch397 :
    (∑ n ∈ Finset.Icc 89474 89729, roundedTerm 10000000000 n) = 28523584 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 89474 89729 28523584
    (by decide) (by decide) weights397

private theorem weights398 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 89730 89985 = 27968264 := by
  decide +kernel

private theorem batch398 :
    (∑ n ∈ Finset.Icc 89730 89985, roundedTerm 10000000000 n) = 27968264 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 89730 89985 27968264
    (by decide) (by decide) weights398

private theorem weights399 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 89986 90241 = 29038890 := by
  decide +kernel

private theorem batch399 :
    (∑ n ∈ Finset.Icc 89986 90241, roundedTerm 10000000000 n) = 29038890 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 89986 90241 29038890
    (by decide) (by decide) weights399

private theorem weights400 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 90242 90497 = 27614466 := by
  decide +kernel

private theorem batch400 :
    (∑ n ∈ Finset.Icc 90242 90497, roundedTerm 10000000000 n) = 27614466 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 90242 90497 27614466
    (by decide) (by decide) weights400

private theorem weights401 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 90498 90753 = 28297018 := by
  decide +kernel

private theorem batch401 :
    (∑ n ∈ Finset.Icc 90498 90753, roundedTerm 10000000000 n) = 28297018 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 90498 90753 28297018
    (by decide) (by decide) weights401

private theorem weights402 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 90754 91009 = 28844553 := by
  decide +kernel

private theorem batch402 :
    (∑ n ∈ Finset.Icc 90754 91009, roundedTerm 10000000000 n) = 28844553 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 90754 91009 28844553
    (by decide) (by decide) weights402

private theorem weights403 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 91010 91265 = 28505046 := by
  decide +kernel

private theorem batch403 :
    (∑ n ∈ Finset.Icc 91010 91265, roundedTerm 10000000000 n) = 28505046 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 91010 91265 28505046
    (by decide) (by decide) weights403

private theorem weights404 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 91266 91521 = 28657058 := by
  decide +kernel

private theorem batch404 :
    (∑ n ∈ Finset.Icc 91266 91521, roundedTerm 10000000000 n) = 28657058 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 91266 91521 28657058
    (by decide) (by decide) weights404

private theorem weights405 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 91522 91777 = 27119398 := by
  decide +kernel

private theorem batch405 :
    (∑ n ∈ Finset.Icc 91522 91777, roundedTerm 10000000000 n) = 27119398 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 91522 91777 27119398
    (by decide) (by decide) weights405

private theorem weights406 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 91778 92033 = 28316459 := by
  decide +kernel

private theorem batch406 :
    (∑ n ∈ Finset.Icc 91778 92033, roundedTerm 10000000000 n) = 28316459 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 91778 92033 28316459
    (by decide) (by decide) weights406

private theorem weights407 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 92034 92156 = 12699937 := by
  decide +kernel

private theorem batch407 :
    (∑ n ∈ Finset.Icc 92034 92156, roundedTerm 10000000000 n) = 12699937 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 92034 92156 12699937
    (by decide) (by decide) weights407

private theorem weights408 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 92157 92412 = 28167730 := by
  decide +kernel

private theorem batch408 :
    (∑ n ∈ Finset.Icc 92157 92412, roundedTerm 10000000000 n) = 28167730 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 92157 92412 28167730
    (by decide) (by decide) weights408

private theorem weights409 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 92413 92668 = 27751645 := by
  decide +kernel

private theorem batch409 :
    (∑ n ∈ Finset.Icc 92413 92668, roundedTerm 10000000000 n) = 27751645 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 92413 92668 27751645
    (by decide) (by decide) weights409

private theorem weights410 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 92669 92924 = 27500528 := by
  decide +kernel

private theorem batch410 :
    (∑ n ∈ Finset.Icc 92669 92924, roundedTerm 10000000000 n) = 27500528 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 92669 92924 27500528
    (by decide) (by decide) weights410

private theorem weights411 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 92925 93180 = 27373824 := by
  decide +kernel

private theorem batch411 :
    (∑ n ∈ Finset.Icc 92925 93180, roundedTerm 10000000000 n) = 27373824 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 92925 93180 27373824
    (by decide) (by decide) weights411

private theorem weights412 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 93181 93436 = 27729701 := by
  decide +kernel

private theorem batch412 :
    (∑ n ∈ Finset.Icc 93181 93436, roundedTerm 10000000000 n) = 27729701 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 93181 93436 27729701
    (by decide) (by decide) weights412

private theorem weights413 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 93437 93692 = 26520394 := by
  decide +kernel

private theorem batch413 :
    (∑ n ∈ Finset.Icc 93437 93692, roundedTerm 10000000000 n) = 26520394 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 93437 93692 26520394
    (by decide) (by decide) weights413

private theorem weights414 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 93693 93948 = 28037909 := by
  decide +kernel

private theorem batch414 :
    (∑ n ∈ Finset.Icc 93693 93948, roundedTerm 10000000000 n) = 28037909 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 93693 93948 28037909
    (by decide) (by decide) weights414

private theorem weights415 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 93949 94204 = 26851950 := by
  decide +kernel

private theorem batch415 :
    (∑ n ∈ Finset.Icc 93949 94204, roundedTerm 10000000000 n) = 26851950 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 93949 94204 26851950
    (by decide) (by decide) weights415

set_option trace.profiler true in
private theorem weights416 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 94205 94460 = 27511907 := by
  decide +kernel

private theorem batch416 :
    (∑ n ∈ Finset.Icc 94205 94460, roundedTerm 10000000000 n) = 27511907 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 94205 94460 27511907
    (by decide) (by decide) weights416

private theorem weights417 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 94461 94716 = 27020049 := by
  decide +kernel

private theorem batch417 :
    (∑ n ∈ Finset.Icc 94461 94716, roundedTerm 10000000000 n) = 27020049 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 94461 94716 27020049
    (by decide) (by decide) weights417

private theorem weights418 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 94717 94972 = 27467555 := by
  decide +kernel

private theorem batch418 :
    (∑ n ∈ Finset.Icc 94717 94972, roundedTerm 10000000000 n) = 27467555 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 94717 94972 27467555
    (by decide) (by decide) weights418

private theorem weights419 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 94973 95228 = 26702468 := by
  decide +kernel

private theorem batch419 :
    (∑ n ∈ Finset.Icc 94973 95228, roundedTerm 10000000000 n) = 26702468 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 94973 95228 26702468
    (by decide) (by decide) weights419

private theorem weights420 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 95229 95484 = 26633437 := by
  decide +kernel

private theorem batch420 :
    (∑ n ∈ Finset.Icc 95229 95484, roundedTerm 10000000000 n) = 26633437 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 95229 95484 26633437
    (by decide) (by decide) weights420

private theorem weights421 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 95485 95740 = 26965982 := by
  decide +kernel

private theorem batch421 :
    (∑ n ∈ Finset.Icc 95485 95740, roundedTerm 10000000000 n) = 26965982 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 95485 95740 26965982
    (by decide) (by decide) weights421

private theorem weights422 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 95741 95996 = 26013057 := by
  decide +kernel

private theorem batch422 :
    (∑ n ∈ Finset.Icc 95741 95996, roundedTerm 10000000000 n) = 26013057 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 95741 95996 26013057
    (by decide) (by decide) weights422

private theorem weights423 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 95997 96252 = 26806151 := by
  decide +kernel

private theorem batch423 :
    (∑ n ∈ Finset.Icc 95997 96252, roundedTerm 10000000000 n) = 26806151 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 95997 96252 26806151
    (by decide) (by decide) weights423

private theorem weights424 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 96253 96508 = 25846453 := by
  decide +kernel

private theorem batch424 :
    (∑ n ∈ Finset.Icc 96253 96508, roundedTerm 10000000000 n) = 25846453 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 96253 96508 25846453
    (by decide) (by decide) weights424

private theorem weights425 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 96509 96764 = 26193590 := by
  decide +kernel

private theorem batch425 :
    (∑ n ∈ Finset.Icc 96509 96764, roundedTerm 10000000000 n) = 26193590 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 96509 96764 26193590
    (by decide) (by decide) weights425

private theorem weights426 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 96765 97020 = 26686035 := by
  decide +kernel

private theorem batch426 :
    (∑ n ∈ Finset.Icc 96765 97020, roundedTerm 10000000000 n) = 26686035 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 96765 97020 26686035
    (by decide) (by decide) weights426

private theorem weights427 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 97021 97276 = 26111540 := by
  decide +kernel

private theorem batch427 :
    (∑ n ∈ Finset.Icc 97021 97276, roundedTerm 10000000000 n) = 26111540 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 97021 97276 26111540
    (by decide) (by decide) weights427

private theorem weights428 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 97277 97532 = 26372721 := by
  decide +kernel

private theorem batch428 :
    (∑ n ∈ Finset.Icc 97277 97532, roundedTerm 10000000000 n) = 26372721 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 97277 97532 26372721
    (by decide) (by decide) weights428

private theorem weights429 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 97533 97788 = 26486322 := by
  decide +kernel

private theorem batch429 :
    (∑ n ∈ Finset.Icc 97533 97788, roundedTerm 10000000000 n) = 26486322 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 97533 97788 26486322
    (by decide) (by decide) weights429

private theorem weights430 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 97789 98044 = 26354640 := by
  decide +kernel

private theorem batch430 :
    (∑ n ∈ Finset.Icc 97789 98044, roundedTerm 10000000000 n) = 26354640 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 97789 98044 26354640
    (by decide) (by decide) weights430

private theorem weights431 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 98045 98300 = 25680176 := by
  decide +kernel

private theorem batch431 :
    (∑ n ∈ Finset.Icc 98045 98300, roundedTerm 10000000000 n) = 25680176 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 98045 98300 25680176
    (by decide) (by decide) weights431

private theorem weights432 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 98301 98556 = 25416205 := by
  decide +kernel

private theorem batch432 :
    (∑ n ∈ Finset.Icc 98301 98556, roundedTerm 10000000000 n) = 25416205 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 98301 98556 25416205
    (by decide) (by decide) weights432

private theorem weights433 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 98557 98812 = 26650764 := by
  decide +kernel

private theorem batch433 :
    (∑ n ∈ Finset.Icc 98557 98812, roundedTerm 10000000000 n) = 26650764 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 98557 98812 26650764
    (by decide) (by decide) weights433

private theorem weights434 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 98813 99068 = 25482895 := by
  decide +kernel

private theorem batch434 :
    (∑ n ∈ Finset.Icc 98813 99068, roundedTerm 10000000000 n) = 25482895 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 98813 99068 25482895
    (by decide) (by decide) weights434

private theorem weights435 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 99069 99324 = 26163624 := by
  decide +kernel

private theorem batch435 :
    (∑ n ∈ Finset.Icc 99069 99324, roundedTerm 10000000000 n) = 26163624 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 99069 99324 26163624
    (by decide) (by decide) weights435

private theorem weights436 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 99325 99580 = 25902987 := by
  decide +kernel

private theorem batch436 :
    (∑ n ∈ Finset.Icc 99325 99580, roundedTerm 10000000000 n) = 25902987 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 99325 99580 25902987
    (by decide) (by decide) weights436

private theorem weights437 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 99581 99836 = 26298198 := by
  decide +kernel

private theorem batch437 :
    (∑ n ∈ Finset.Icc 99581 99836, roundedTerm 10000000000 n) = 26298198 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 99581 99836 26298198
    (by decide) (by decide) weights437

private theorem weights438 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 99837 100092 = 24853972 := by
  decide +kernel

private theorem batch438 :
    (∑ n ∈ Finset.Icc 99837 100092, roundedTerm 10000000000 n) = 24853972 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 99837 100092 24853972
    (by decide) (by decide) weights438

private theorem weights439 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 100093 100348 = 26386121 := by
  decide +kernel

private theorem batch439 :
    (∑ n ∈ Finset.Icc 100093 100348, roundedTerm 10000000000 n) = 26386121 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 100093 100348 26386121
    (by decide) (by decide) weights439

private theorem weights440 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 100349 100604 = 25261429 := by
  decide +kernel

private theorem batch440 :
    (∑ n ∈ Finset.Icc 100349 100604, roundedTerm 10000000000 n) = 25261429 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 100349 100604 25261429
    (by decide) (by decide) weights440

private theorem weights441 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 100605 100860 = 25639220 := by
  decide +kernel

private theorem batch441 :
    (∑ n ∈ Finset.Icc 100605 100860, roundedTerm 10000000000 n) = 25639220 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 100605 100860 25639220
    (by decide) (by decide) weights441

private theorem weights442 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 100861 101116 = 24966987 := by
  decide +kernel

private theorem batch442 :
    (∑ n ∈ Finset.Icc 100861 101116, roundedTerm 10000000000 n) = 24966987 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 100861 101116 24966987
    (by decide) (by decide) weights442

private theorem weights443 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 101117 101372 = 25954015 := by
  decide +kernel

private theorem batch443 :
    (∑ n ∈ Finset.Icc 101117 101372, roundedTerm 10000000000 n) = 25954015 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 101117 101372 25954015
    (by decide) (by decide) weights443

private theorem weights444 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 101373 101628 = 25265617 := by
  decide +kernel

private theorem batch444 :
    (∑ n ∈ Finset.Icc 101373 101628, roundedTerm 10000000000 n) = 25265617 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 101373 101628 25265617
    (by decide) (by decide) weights444

private theorem weights445 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 101629 101884 = 24693883 := by
  decide +kernel

private theorem batch445 :
    (∑ n ∈ Finset.Icc 101629 101884, roundedTerm 10000000000 n) = 24693883 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 101629 101884 24693883
    (by decide) (by decide) weights445

private theorem weights446 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 101885 102140 = 25735221 := by
  decide +kernel

private theorem batch446 :
    (∑ n ∈ Finset.Icc 101885 102140, roundedTerm 10000000000 n) = 25735221 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 101885 102140 25735221
    (by decide) (by decide) weights446

private theorem weights447 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 102141 102396 = 25320394 := by
  decide +kernel

private theorem batch447 :
    (∑ n ∈ Finset.Icc 102141 102396, roundedTerm 10000000000 n) = 25320394 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 102141 102396 25320394
    (by decide) (by decide) weights447

set_option trace.profiler true in
private theorem weights448 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 102397 102652 = 24072012 := by
  decide +kernel

private theorem batch448 :
    (∑ n ∈ Finset.Icc 102397 102652, roundedTerm 10000000000 n) = 24072012 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 102397 102652 24072012
    (by decide) (by decide) weights448

private theorem weights449 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 102653 102908 = 25248226 := by
  decide +kernel

private theorem batch449 :
    (∑ n ∈ Finset.Icc 102653 102908, roundedTerm 10000000000 n) = 25248226 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 102653 102908 25248226
    (by decide) (by decide) weights449

private theorem weights450 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 102909 103164 = 24289907 := by
  decide +kernel

private theorem batch450 :
    (∑ n ∈ Finset.Icc 102909 103164, roundedTerm 10000000000 n) = 24289907 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 102909 103164 24289907
    (by decide) (by decide) weights450

private theorem weights451 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 103165 103420 = 24555551 := by
  decide +kernel

private theorem batch451 :
    (∑ n ∈ Finset.Icc 103165 103420, roundedTerm 10000000000 n) = 24555551 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 103165 103420 24555551
    (by decide) (by decide) weights451

private theorem weights452 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 103421 103676 = 24653294 := by
  decide +kernel

private theorem batch452 :
    (∑ n ∈ Finset.Icc 103421 103676, roundedTerm 10000000000 n) = 24653294 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 103421 103676 24653294
    (by decide) (by decide) weights452

private theorem weights453 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 103677 103932 = 24786431 := by
  decide +kernel

private theorem batch453 :
    (∑ n ∈ Finset.Icc 103677 103932, roundedTerm 10000000000 n) = 24786431 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 103677 103932 24786431
    (by decide) (by decide) weights453

private theorem weights454 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 103933 104188 = 25036403 := by
  decide +kernel

private theorem batch454 :
    (∑ n ∈ Finset.Icc 103933 104188, roundedTerm 10000000000 n) = 25036403 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 103933 104188 25036403
    (by decide) (by decide) weights454

private theorem weights455 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 104189 104444 = 23799950 := by
  decide +kernel

private theorem batch455 :
    (∑ n ∈ Finset.Icc 104189 104444, roundedTerm 10000000000 n) = 23799950 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 104189 104444 23799950
    (by decide) (by decide) weights455

private theorem weights456 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 104445 104700 = 24453394 := by
  decide +kernel

private theorem batch456 :
    (∑ n ∈ Finset.Icc 104445 104700, roundedTerm 10000000000 n) = 24453394 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 104445 104700 24453394
    (by decide) (by decide) weights456

private theorem weights457 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 104701 104956 = 24645315 := by
  decide +kernel

private theorem batch457 :
    (∑ n ∈ Finset.Icc 104701 104956, roundedTerm 10000000000 n) = 24645315 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 104701 104956 24645315
    (by decide) (by decide) weights457

private theorem weights458 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 104957 105212 = 24471930 := by
  decide +kernel

private theorem batch458 :
    (∑ n ∈ Finset.Icc 104957 105212, roundedTerm 10000000000 n) = 24471930 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 104957 105212 24471930
    (by decide) (by decide) weights458

private theorem weights459 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 105213 105468 = 24309813 := by
  decide +kernel

private theorem batch459 :
    (∑ n ∈ Finset.Icc 105213 105468, roundedTerm 10000000000 n) = 24309813 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 105213 105468 24309813
    (by decide) (by decide) weights459

private theorem weights460 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 105469 105724 = 24645138 := by
  decide +kernel

private theorem batch460 :
    (∑ n ∈ Finset.Icc 105469 105724, roundedTerm 10000000000 n) = 24645138 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 105469 105724 24645138
    (by decide) (by decide) weights460

private theorem weights461 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 105725 105818 = 8726865 := by
  decide +kernel

private theorem batch461 :
    (∑ n ∈ Finset.Icc 105725 105818, roundedTerm 10000000000 n) = 8726865 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 105725 105818 8726865
    (by decide) (by decide) weights461

private theorem weights462 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 105819 106074 = 24264360 := by
  decide +kernel

private theorem batch462 :
    (∑ n ∈ Finset.Icc 105819 106074, roundedTerm 10000000000 n) = 24264360 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 105819 106074 24264360
    (by decide) (by decide) weights462

private theorem weights463 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 106075 106330 = 23677669 := by
  decide +kernel

private theorem batch463 :
    (∑ n ∈ Finset.Icc 106075 106330, roundedTerm 10000000000 n) = 23677669 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 106075 106330 23677669
    (by decide) (by decide) weights463

private theorem weights464 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 106331 106586 = 24511342 := by
  decide +kernel

private theorem batch464 :
    (∑ n ∈ Finset.Icc 106331 106586, roundedTerm 10000000000 n) = 24511342 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 106331 106586 24511342
    (by decide) (by decide) weights464

private theorem weights465 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 106587 106842 = 24489564 := by
  decide +kernel

private theorem batch465 :
    (∑ n ∈ Finset.Icc 106587 106842, roundedTerm 10000000000 n) = 24489564 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 106587 106842 24489564
    (by decide) (by decide) weights465

private theorem weights466 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 106843 107098 = 23726120 := by
  decide +kernel

private theorem batch466 :
    (∑ n ∈ Finset.Icc 106843 107098, roundedTerm 10000000000 n) = 23726120 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 106843 107098 23726120
    (by decide) (by decide) weights466

private theorem weights467 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 107099 107354 = 23393381 := by
  decide +kernel

private theorem batch467 :
    (∑ n ∈ Finset.Icc 107099 107354, roundedTerm 10000000000 n) = 23393381 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 107099 107354 23393381
    (by decide) (by decide) weights467

private theorem weights468 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 107355 107610 = 24516992 := by
  decide +kernel

private theorem batch468 :
    (∑ n ∈ Finset.Icc 107355 107610, roundedTerm 10000000000 n) = 24516992 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 107355 107610 24516992
    (by decide) (by decide) weights468

private theorem weights469 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 107611 107866 = 23730647 := by
  decide +kernel

private theorem batch469 :
    (∑ n ∈ Finset.Icc 107611 107866, roundedTerm 10000000000 n) = 23730647 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 107611 107866 23730647
    (by decide) (by decide) weights469

private theorem weights470 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 107867 108122 = 23783417 := by
  decide +kernel

private theorem batch470 :
    (∑ n ∈ Finset.Icc 107867 108122, roundedTerm 10000000000 n) = 23783417 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 107867 108122 23783417
    (by decide) (by decide) weights470

private theorem weights471 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 108123 108378 = 23264892 := by
  decide +kernel

private theorem batch471 :
    (∑ n ∈ Finset.Icc 108123 108378, roundedTerm 10000000000 n) = 23264892 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 108123 108378 23264892
    (by decide) (by decide) weights471

private theorem weights472 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 108379 108634 = 23935356 := by
  decide +kernel

private theorem batch472 :
    (∑ n ∈ Finset.Icc 108379 108634, roundedTerm 10000000000 n) = 23935356 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 108379 108634 23935356
    (by decide) (by decide) weights472

private theorem weights473 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 108635 108890 = 23574876 := by
  decide +kernel

private theorem batch473 :
    (∑ n ∈ Finset.Icc 108635 108890, roundedTerm 10000000000 n) = 23574876 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 108635 108890 23574876
    (by decide) (by decide) weights473

private theorem weights474 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 108891 109146 = 23358256 := by
  decide +kernel

private theorem batch474 :
    (∑ n ∈ Finset.Icc 108891 109146, roundedTerm 10000000000 n) = 23358256 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 108891 109146 23358256
    (by decide) (by decide) weights474

private theorem weights475 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 109147 109402 = 23253800 := by
  decide +kernel

private theorem batch475 :
    (∑ n ∈ Finset.Icc 109147 109402, roundedTerm 10000000000 n) = 23253800 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 109147 109402 23253800
    (by decide) (by decide) weights475

private theorem weights476 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 109403 109658 = 22834543 := by
  decide +kernel

private theorem batch476 :
    (∑ n ∈ Finset.Icc 109403 109658, roundedTerm 10000000000 n) = 22834543 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 109403 109658 22834543
    (by decide) (by decide) weights476

private theorem weights477 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 109659 109914 = 23769409 := by
  decide +kernel

private theorem batch477 :
    (∑ n ∈ Finset.Icc 109659 109914, roundedTerm 10000000000 n) = 23769409 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 109659 109914 23769409
    (by decide) (by decide) weights477

private theorem weights478 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 109915 110170 = 23268033 := by
  decide +kernel

private theorem batch478 :
    (∑ n ∈ Finset.Icc 109915 110170, roundedTerm 10000000000 n) = 23268033 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 109915 110170 23268033
    (by decide) (by decide) weights478

private theorem weights479 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 110171 110426 = 23827366 := by
  decide +kernel

private theorem batch479 :
    (∑ n ∈ Finset.Icc 110171 110426, roundedTerm 10000000000 n) = 23827366 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 110171 110426 23827366
    (by decide) (by decide) weights479

set_option trace.profiler true in
private theorem weights480 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 110427 110682 = 22655042 := by
  decide +kernel

private theorem batch480 :
    (∑ n ∈ Finset.Icc 110427 110682, roundedTerm 10000000000 n) = 22655042 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 110427 110682 22655042
    (by decide) (by decide) weights480

private theorem weights481 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 110683 110938 = 23101632 := by
  decide +kernel

private theorem batch481 :
    (∑ n ∈ Finset.Icc 110683 110938, roundedTerm 10000000000 n) = 23101632 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 110683 110938 23101632
    (by decide) (by decide) weights481

private theorem weights482 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 110939 111194 = 22799175 := by
  decide +kernel

private theorem batch482 :
    (∑ n ∈ Finset.Icc 110939 111194, roundedTerm 10000000000 n) = 22799175 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 110939 111194 22799175
    (by decide) (by decide) weights482

private theorem weights483 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 111195 111450 = 22762056 := by
  decide +kernel

private theorem batch483 :
    (∑ n ∈ Finset.Icc 111195 111450, roundedTerm 10000000000 n) = 22762056 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 111195 111450 22762056
    (by decide) (by decide) weights483

private theorem weights484 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 111451 111706 = 22807337 := by
  decide +kernel

private theorem batch484 :
    (∑ n ∈ Finset.Icc 111451 111706, roundedTerm 10000000000 n) = 22807337 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 111451 111706 22807337
    (by decide) (by decide) weights484

private theorem weights485 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 111707 111962 = 22774261 := by
  decide +kernel

private theorem batch485 :
    (∑ n ∈ Finset.Icc 111707 111962, roundedTerm 10000000000 n) = 22774261 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 111707 111962 22774261
    (by decide) (by decide) weights485

private theorem weights486 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 111963 112218 = 23469481 := by
  decide +kernel

private theorem batch486 :
    (∑ n ∈ Finset.Icc 111963 112218, roundedTerm 10000000000 n) = 23469481 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 111963 112218 23469481
    (by decide) (by decide) weights486

private theorem weights487 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 112219 112474 = 22756842 := by
  decide +kernel

private theorem batch487 :
    (∑ n ∈ Finset.Icc 112219 112474, roundedTerm 10000000000 n) = 22756842 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 112219 112474 22756842
    (by decide) (by decide) weights487

private theorem weights488 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 112475 112730 = 21838205 := by
  decide +kernel

private theorem batch488 :
    (∑ n ∈ Finset.Icc 112475 112730, roundedTerm 10000000000 n) = 21838205 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 112475 112730 21838205
    (by decide) (by decide) weights488

private theorem weights489 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 112731 112986 = 22943074 := by
  decide +kernel

private theorem batch489 :
    (∑ n ∈ Finset.Icc 112731 112986, roundedTerm 10000000000 n) = 22943074 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 112731 112986 22943074
    (by decide) (by decide) weights489

private theorem weights490 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 112987 113242 = 22020258 := by
  decide +kernel

private theorem batch490 :
    (∑ n ∈ Finset.Icc 112987 113242, roundedTerm 10000000000 n) = 22020258 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 112987 113242 22020258
    (by decide) (by decide) weights490

private theorem weights491 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 113243 113498 = 22479899 := by
  decide +kernel

private theorem batch491 :
    (∑ n ∈ Finset.Icc 113243 113498, roundedTerm 10000000000 n) = 22479899 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 113243 113498 22479899
    (by decide) (by decide) weights491

private theorem weights492 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 113499 113754 = 22463375 := by
  decide +kernel

private theorem batch492 :
    (∑ n ∈ Finset.Icc 113499 113754, roundedTerm 10000000000 n) = 22463375 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 113499 113754 22463375
    (by decide) (by decide) weights492

private theorem weights493 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 113755 114010 = 22882940 := by
  decide +kernel

private theorem batch493 :
    (∑ n ∈ Finset.Icc 113755 114010, roundedTerm 10000000000 n) = 22882940 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 113755 114010 22882940
    (by decide) (by decide) weights493

private theorem weights494 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 114011 114266 = 22688137 := by
  decide +kernel

private theorem batch494 :
    (∑ n ∈ Finset.Icc 114011 114266, roundedTerm 10000000000 n) = 22688137 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 114011 114266 22688137
    (by decide) (by decide) weights494

private theorem weights495 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 114267 114522 = 22407951 := by
  decide +kernel

private theorem batch495 :
    (∑ n ∈ Finset.Icc 114267 114522, roundedTerm 10000000000 n) = 22407951 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 114267 114522 22407951
    (by decide) (by decide) weights495

private theorem weights496 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 114523 114778 = 22160781 := by
  decide +kernel

private theorem batch496 :
    (∑ n ∈ Finset.Icc 114523 114778, roundedTerm 10000000000 n) = 22160781 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 114523 114778 22160781
    (by decide) (by decide) weights496

private theorem weights497 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 114779 115034 = 22252553 := by
  decide +kernel

private theorem batch497 :
    (∑ n ∈ Finset.Icc 114779 115034, roundedTerm 10000000000 n) = 22252553 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 114779 115034 22252553
    (by decide) (by decide) weights497

private theorem weights498 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 115035 115290 = 22149642 := by
  decide +kernel

private theorem batch498 :
    (∑ n ∈ Finset.Icc 115035 115290, roundedTerm 10000000000 n) = 22149642 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 115035 115290 22149642
    (by decide) (by decide) weights498

private theorem weights499 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 115291 115546 = 22338518 := by
  decide +kernel

private theorem batch499 :
    (∑ n ∈ Finset.Icc 115291 115546, roundedTerm 10000000000 n) = 22338518 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 115291 115546 22338518
    (by decide) (by decide) weights499

private theorem weights500 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 115547 115802 = 22588466 := by
  decide +kernel

private theorem batch500 :
    (∑ n ∈ Finset.Icc 115547 115802, roundedTerm 10000000000 n) = 22588466 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 115547 115802 22588466
    (by decide) (by decide) weights500

private theorem weights501 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 115803 116058 = 21326806 := by
  decide +kernel

private theorem batch501 :
    (∑ n ∈ Finset.Icc 115803 116058, roundedTerm 10000000000 n) = 21326806 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 115803 116058 21326806
    (by decide) (by decide) weights501

private theorem weights502 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 116059 116314 = 21760695 := by
  decide +kernel

private theorem batch502 :
    (∑ n ∈ Finset.Icc 116059 116314, roundedTerm 10000000000 n) = 21760695 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 116059 116314 21760695
    (by decide) (by decide) weights502

private theorem weights503 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 116315 116570 = 22232158 := by
  decide +kernel

private theorem batch503 :
    (∑ n ∈ Finset.Icc 116315 116570, roundedTerm 10000000000 n) = 22232158 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 116315 116570 22232158
    (by decide) (by decide) weights503

private theorem weights504 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 116571 116826 = 21779737 := by
  decide +kernel

private theorem batch504 :
    (∑ n ∈ Finset.Icc 116571 116826, roundedTerm 10000000000 n) = 21779737 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 116571 116826 21779737
    (by decide) (by decide) weights504

private theorem weights505 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 116827 117082 = 21731261 := by
  decide +kernel

private theorem batch505 :
    (∑ n ∈ Finset.Icc 116827 117082, roundedTerm 10000000000 n) = 21731261 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 116827 117082 21731261
    (by decide) (by decide) weights505

private theorem weights506 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 117083 117338 = 21627456 := by
  decide +kernel

private theorem batch506 :
    (∑ n ∈ Finset.Icc 117083 117338, roundedTerm 10000000000 n) = 21627456 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 117083 117338 21627456
    (by decide) (by decide) weights506

private theorem weights507 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 117339 117594 = 21660490 := by
  decide +kernel

private theorem batch507 :
    (∑ n ∈ Finset.Icc 117339 117594, roundedTerm 10000000000 n) = 21660490 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 117339 117594 21660490
    (by decide) (by decide) weights507

private theorem weights508 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 117595 117850 = 21521324 := by
  decide +kernel

private theorem batch508 :
    (∑ n ∈ Finset.Icc 117595 117850, roundedTerm 10000000000 n) = 21521324 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 117595 117850 21521324
    (by decide) (by decide) weights508

private theorem weights509 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 117851 118106 = 21200695 := by
  decide +kernel

private theorem batch509 :
    (∑ n ∈ Finset.Icc 117851 118106, roundedTerm 10000000000 n) = 21200695 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 117851 118106 21200695
    (by decide) (by decide) weights509

private theorem weights510 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 118107 118362 = 21518278 := by
  decide +kernel

private theorem batch510 :
    (∑ n ∈ Finset.Icc 118107 118362, roundedTerm 10000000000 n) = 21518278 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 118107 118362 21518278
    (by decide) (by decide) weights510

private theorem weights511 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 118363 118618 = 21987118 := by
  decide +kernel

private theorem batch511 :
    (∑ n ∈ Finset.Icc 118363 118618, roundedTerm 10000000000 n) = 21987118 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 118363 118618 21987118
    (by decide) (by decide) weights511

set_option trace.profiler true in
private theorem weights512 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 118619 118874 = 21030655 := by
  decide +kernel

private theorem batch512 :
    (∑ n ∈ Finset.Icc 118619 118874, roundedTerm 10000000000 n) = 21030655 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 118619 118874 21030655
    (by decide) (by decide) weights512

private theorem weights513 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 118875 119130 = 21921269 := by
  decide +kernel

private theorem batch513 :
    (∑ n ∈ Finset.Icc 118875 119130, roundedTerm 10000000000 n) = 21921269 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 118875 119130 21921269
    (by decide) (by decide) weights513

private theorem weights514 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 119131 119386 = 21255277 := by
  decide +kernel

private theorem batch514 :
    (∑ n ∈ Finset.Icc 119131 119386, roundedTerm 10000000000 n) = 21255277 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 119131 119386 21255277
    (by decide) (by decide) weights514

private theorem weights515 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 119387 119642 = 21568303 := by
  decide +kernel

private theorem batch515 :
    (∑ n ∈ Finset.Icc 119387 119642, roundedTerm 10000000000 n) = 21568303 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 119387 119642 21568303
    (by decide) (by decide) weights515

private theorem weights516 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 119643 119898 = 21300514 := by
  decide +kernel

private theorem batch516 :
    (∑ n ∈ Finset.Icc 119643 119898, roundedTerm 10000000000 n) = 21300514 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 119643 119898 21300514
    (by decide) (by decide) weights516

private theorem weights517 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 119899 120154 = 21671286 := by
  decide +kernel

private theorem batch517 :
    (∑ n ∈ Finset.Icc 119899 120154, roundedTerm 10000000000 n) = 21671286 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 119899 120154 21671286
    (by decide) (by decide) weights517

private theorem weights518 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 120155 120410 = 21534141 := by
  decide +kernel

private theorem batch518 :
    (∑ n ∈ Finset.Icc 120155 120410, roundedTerm 10000000000 n) = 21534141 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 120155 120410 21534141
    (by decide) (by decide) weights518

private theorem weights519 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 120411 120666 = 20812537 := by
  decide +kernel

private theorem batch519 :
    (∑ n ∈ Finset.Icc 120411 120666, roundedTerm 10000000000 n) = 20812537 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 120411 120666 20812537
    (by decide) (by decide) weights519

private theorem weights520 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 120667 120922 = 21457000 := by
  decide +kernel

private theorem batch520 :
    (∑ n ∈ Finset.Icc 120667 120922, roundedTerm 10000000000 n) = 21457000 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 120667 120922 21457000
    (by decide) (by decide) weights520

private theorem weights521 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 120923 121178 = 21267184 := by
  decide +kernel

private theorem batch521 :
    (∑ n ∈ Finset.Icc 120923 121178, roundedTerm 10000000000 n) = 21267184 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 120923 121178 21267184
    (by decide) (by decide) weights521

private theorem weights522 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 121179 121434 = 21394464 := by
  decide +kernel

private theorem batch522 :
    (∑ n ∈ Finset.Icc 121179 121434, roundedTerm 10000000000 n) = 21394464 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 121179 121434 21394464
    (by decide) (by decide) weights522

private theorem weights523 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 121435 121525 = 7301491 := by
  decide +kernel

private theorem batch523 :
    (∑ n ∈ Finset.Icc 121435 121525, roundedTerm 10000000000 n) = 7301491 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 121435 121525 7301491
    (by decide) (by decide) weights523

private theorem weights524 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 121526 121781 = 20702707 := by
  decide +kernel

private theorem batch524 :
    (∑ n ∈ Finset.Icc 121526 121781, roundedTerm 10000000000 n) = 20702707 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 121526 121781 20702707
    (by decide) (by decide) weights524

private theorem weights525 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 121782 122037 = 20547326 := by
  decide +kernel

private theorem batch525 :
    (∑ n ∈ Finset.Icc 121782 122037, roundedTerm 10000000000 n) = 20547326 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 121782 122037 20547326
    (by decide) (by decide) weights525

private theorem weights526 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 122038 122293 = 20948369 := by
  decide +kernel

private theorem batch526 :
    (∑ n ∈ Finset.Icc 122038 122293, roundedTerm 10000000000 n) = 20948369 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 122038 122293 20948369
    (by decide) (by decide) weights526

private theorem weights527 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 122294 122549 = 21240695 := by
  decide +kernel

private theorem batch527 :
    (∑ n ∈ Finset.Icc 122294 122549, roundedTerm 10000000000 n) = 21240695 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 122294 122549 21240695
    (by decide) (by decide) weights527

private theorem weights528 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 122550 122805 = 20695952 := by
  decide +kernel

private theorem batch528 :
    (∑ n ∈ Finset.Icc 122550 122805, roundedTerm 10000000000 n) = 20695952 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 122550 122805 20695952
    (by decide) (by decide) weights528

private theorem weights529 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 122806 123061 = 21375458 := by
  decide +kernel

private theorem batch529 :
    (∑ n ∈ Finset.Icc 122806 123061, roundedTerm 10000000000 n) = 21375458 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 122806 123061 21375458
    (by decide) (by decide) weights529

private theorem weights530 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 123062 123317 = 20851872 := by
  decide +kernel

private theorem batch530 :
    (∑ n ∈ Finset.Icc 123062 123317, roundedTerm 10000000000 n) = 20851872 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 123062 123317 20851872
    (by decide) (by decide) weights530

private theorem weights531 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 123318 123573 = 20572195 := by
  decide +kernel

private theorem batch531 :
    (∑ n ∈ Finset.Icc 123318 123573, roundedTerm 10000000000 n) = 20572195 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 123318 123573 20572195
    (by decide) (by decide) weights531

private theorem weights532 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 123574 123829 = 20939770 := by
  decide +kernel

private theorem batch532 :
    (∑ n ∈ Finset.Icc 123574 123829, roundedTerm 10000000000 n) = 20939770 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 123574 123829 20939770
    (by decide) (by decide) weights532

private theorem weights533 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 123830 124085 = 20793419 := by
  decide +kernel

private theorem batch533 :
    (∑ n ∈ Finset.Icc 123830 124085, roundedTerm 10000000000 n) = 20793419 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 123830 124085 20793419
    (by decide) (by decide) weights533

private theorem weights534 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 124086 124341 = 20911713 := by
  decide +kernel

private theorem batch534 :
    (∑ n ∈ Finset.Icc 124086 124341, roundedTerm 10000000000 n) = 20911713 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 124086 124341 20911713
    (by decide) (by decide) weights534

private theorem weights535 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 124342 124597 = 20630053 := by
  decide +kernel

private theorem batch535 :
    (∑ n ∈ Finset.Icc 124342 124597, roundedTerm 10000000000 n) = 20630053 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 124342 124597 20630053
    (by decide) (by decide) weights535

private theorem weights536 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 124598 124853 = 20949156 := by
  decide +kernel

private theorem batch536 :
    (∑ n ∈ Finset.Icc 124598 124853, roundedTerm 10000000000 n) = 20949156 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 124598 124853 20949156
    (by decide) (by decide) weights536

private theorem weights537 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 124854 125109 = 20815339 := by
  decide +kernel

private theorem batch537 :
    (∑ n ∈ Finset.Icc 124854 125109, roundedTerm 10000000000 n) = 20815339 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 124854 125109 20815339
    (by decide) (by decide) weights537

private theorem weights538 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 125110 125365 = 20383674 := by
  decide +kernel

private theorem batch538 :
    (∑ n ∈ Finset.Icc 125110 125365, roundedTerm 10000000000 n) = 20383674 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 125110 125365 20383674
    (by decide) (by decide) weights538

private theorem weights539 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 125366 125621 = 20272687 := by
  decide +kernel

private theorem batch539 :
    (∑ n ∈ Finset.Icc 125366 125621, roundedTerm 10000000000 n) = 20272687 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 125366 125621 20272687
    (by decide) (by decide) weights539

private theorem weights540 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 125622 125877 = 20618015 := by
  decide +kernel

private theorem batch540 :
    (∑ n ∈ Finset.Icc 125622 125877, roundedTerm 10000000000 n) = 20618015 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 125622 125877 20618015
    (by decide) (by decide) weights540

private theorem weights541 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 125878 126133 = 19636991 := by
  decide +kernel

private theorem batch541 :
    (∑ n ∈ Finset.Icc 125878 126133, roundedTerm 10000000000 n) = 19636991 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 125878 126133 19636991
    (by decide) (by decide) weights541

private theorem weights542 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 126134 126389 = 20600405 := by
  decide +kernel

private theorem batch542 :
    (∑ n ∈ Finset.Icc 126134 126389, roundedTerm 10000000000 n) = 20600405 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 126134 126389 20600405
    (by decide) (by decide) weights542

private theorem weights543 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 126390 126645 = 20581061 := by
  decide +kernel

private theorem batch543 :
    (∑ n ∈ Finset.Icc 126390 126645, roundedTerm 10000000000 n) = 20581061 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 126390 126645 20581061
    (by decide) (by decide) weights543

set_option trace.profiler true in
private theorem weights544 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 126646 126901 = 20379489 := by
  decide +kernel

private theorem batch544 :
    (∑ n ∈ Finset.Icc 126646 126901, roundedTerm 10000000000 n) = 20379489 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 126646 126901 20379489
    (by decide) (by decide) weights544

private theorem weights545 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 126902 127157 = 20175637 := by
  decide +kernel

private theorem batch545 :
    (∑ n ∈ Finset.Icc 126902 127157, roundedTerm 10000000000 n) = 20175637 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 126902 127157 20175637
    (by decide) (by decide) weights545

private theorem weights546 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 127158 127413 = 20764634 := by
  decide +kernel

private theorem batch546 :
    (∑ n ∈ Finset.Icc 127158 127413, roundedTerm 10000000000 n) = 20764634 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 127158 127413 20764634
    (by decide) (by decide) weights546

private theorem weights547 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 127414 127669 = 19878597 := by
  decide +kernel

private theorem batch547 :
    (∑ n ∈ Finset.Icc 127414 127669, roundedTerm 10000000000 n) = 19878597 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 127414 127669 19878597
    (by decide) (by decide) weights547

private theorem weights548 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 127670 127925 = 19836827 := by
  decide +kernel

private theorem batch548 :
    (∑ n ∈ Finset.Icc 127670 127925, roundedTerm 10000000000 n) = 19836827 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 127670 127925 19836827
    (by decide) (by decide) weights548

private theorem weights549 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 127926 128181 = 19470928 := by
  decide +kernel

private theorem batch549 :
    (∑ n ∈ Finset.Icc 127926 128181, roundedTerm 10000000000 n) = 19470928 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 127926 128181 19470928
    (by decide) (by decide) weights549

private theorem weights550 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 128182 128437 = 20756881 := by
  decide +kernel

private theorem batch550 :
    (∑ n ∈ Finset.Icc 128182 128437, roundedTerm 10000000000 n) = 20756881 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 128182 128437 20756881
    (by decide) (by decide) weights550

private theorem weights551 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 128438 128693 = 19845308 := by
  decide +kernel

private theorem batch551 :
    (∑ n ∈ Finset.Icc 128438 128693, roundedTerm 10000000000 n) = 19845308 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 128438 128693 19845308
    (by decide) (by decide) weights551

private theorem weights552 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 128694 128949 = 19481098 := by
  decide +kernel

private theorem batch552 :
    (∑ n ∈ Finset.Icc 128694 128949, roundedTerm 10000000000 n) = 19481098 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 128694 128949 19481098
    (by decide) (by decide) weights552

private theorem weights553 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 128950 129205 = 20138201 := by
  decide +kernel

private theorem batch553 :
    (∑ n ∈ Finset.Icc 128950 129205, roundedTerm 10000000000 n) = 20138201 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 128950 129205 20138201
    (by decide) (by decide) weights553

private theorem weights554 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 129206 129461 = 19455114 := by
  decide +kernel

private theorem batch554 :
    (∑ n ∈ Finset.Icc 129206 129461, roundedTerm 10000000000 n) = 19455114 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 129206 129461 19455114
    (by decide) (by decide) weights554

private theorem weights555 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 129462 129717 = 19957463 := by
  decide +kernel

private theorem batch555 :
    (∑ n ∈ Finset.Icc 129462 129717, roundedTerm 10000000000 n) = 19957463 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 129462 129717 19957463
    (by decide) (by decide) weights555

private theorem weights556 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 129718 129973 = 20042971 := by
  decide +kernel

private theorem batch556 :
    (∑ n ∈ Finset.Icc 129718 129973, roundedTerm 10000000000 n) = 20042971 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 129718 129973 20042971
    (by decide) (by decide) weights556

private theorem weights557 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 129974 130229 = 19903829 := by
  decide +kernel

private theorem batch557 :
    (∑ n ∈ Finset.Icc 129974 130229, roundedTerm 10000000000 n) = 19903829 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 129974 130229 19903829
    (by decide) (by decide) weights557

private theorem weights558 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 130230 130485 = 19090072 := by
  decide +kernel

private theorem batch558 :
    (∑ n ∈ Finset.Icc 130230 130485, roundedTerm 10000000000 n) = 19090072 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 130230 130485 19090072
    (by decide) (by decide) weights558

private theorem weights559 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 130486 130741 = 19743528 := by
  decide +kernel

private theorem batch559 :
    (∑ n ∈ Finset.Icc 130486 130741, roundedTerm 10000000000 n) = 19743528 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 130486 130741 19743528
    (by decide) (by decide) weights559

private theorem weights560 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 130742 130997 = 19704644 := by
  decide +kernel

private theorem batch560 :
    (∑ n ∈ Finset.Icc 130742 130997, roundedTerm 10000000000 n) = 19704644 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 130742 130997 19704644
    (by decide) (by decide) weights560

private theorem weights561 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 130998 131253 = 19404092 := by
  decide +kernel

private theorem batch561 :
    (∑ n ∈ Finset.Icc 130998 131253, roundedTerm 10000000000 n) = 19404092 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 130998 131253 19404092
    (by decide) (by decide) weights561

private theorem weights562 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 131254 131509 = 19281796 := by
  decide +kernel

private theorem batch562 :
    (∑ n ∈ Finset.Icc 131254 131509, roundedTerm 10000000000 n) = 19281796 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 131254 131509 19281796
    (by decide) (by decide) weights562

private theorem weights563 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 131510 131765 = 19365740 := by
  decide +kernel

private theorem batch563 :
    (∑ n ∈ Finset.Icc 131510 131765, roundedTerm 10000000000 n) = 19365740 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 131510 131765 19365740
    (by decide) (by decide) weights563

private theorem weights564 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 131766 132021 = 19771314 := by
  decide +kernel

private theorem batch564 :
    (∑ n ∈ Finset.Icc 131766 132021, roundedTerm 10000000000 n) = 19771314 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 131766 132021 19771314
    (by decide) (by decide) weights564

private theorem weights565 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 132022 132277 = 18796649 := by
  decide +kernel

private theorem batch565 :
    (∑ n ∈ Finset.Icc 132022 132277, roundedTerm 10000000000 n) = 18796649 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 132022 132277 18796649
    (by decide) (by decide) weights565

private theorem weights566 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 132278 132533 = 19479508 := by
  decide +kernel

private theorem batch566 :
    (∑ n ∈ Finset.Icc 132278 132533, roundedTerm 10000000000 n) = 19479508 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 132278 132533 19479508
    (by decide) (by decide) weights566

private theorem weights567 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 132534 132789 = 19226335 := by
  decide +kernel

private theorem batch567 :
    (∑ n ∈ Finset.Icc 132534 132789, roundedTerm 10000000000 n) = 19226335 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 132534 132789 19226335
    (by decide) (by decide) weights567

private theorem weights568 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 132790 133045 = 19023170 := by
  decide +kernel

private theorem batch568 :
    (∑ n ∈ Finset.Icc 132790 133045, roundedTerm 10000000000 n) = 19023170 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 132790 133045 19023170
    (by decide) (by decide) weights568

private theorem weights569 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 133046 133301 = 19306664 := by
  decide +kernel

private theorem batch569 :
    (∑ n ∈ Finset.Icc 133046 133301, roundedTerm 10000000000 n) = 19306664 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 133046 133301 19306664
    (by decide) (by decide) weights569

private theorem weights570 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 133302 133557 = 19056353 := by
  decide +kernel

private theorem batch570 :
    (∑ n ∈ Finset.Icc 133302 133557, roundedTerm 10000000000 n) = 19056353 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 133302 133557 19056353
    (by decide) (by decide) weights570

private theorem weights571 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 133558 133813 = 19068765 := by
  decide +kernel

private theorem batch571 :
    (∑ n ∈ Finset.Icc 133558 133813, roundedTerm 10000000000 n) = 19068765 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 133558 133813 19068765
    (by decide) (by decide) weights571

private theorem weights572 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 133814 134069 = 19096244 := by
  decide +kernel

private theorem batch572 :
    (∑ n ∈ Finset.Icc 133814 134069, roundedTerm 10000000000 n) = 19096244 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 133814 134069 19096244
    (by decide) (by decide) weights572

private theorem weights573 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 134070 134325 = 19186235 := by
  decide +kernel

private theorem batch573 :
    (∑ n ∈ Finset.Icc 134070 134325, roundedTerm 10000000000 n) = 19186235 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 134070 134325 19186235
    (by decide) (by decide) weights573

private theorem weights574 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 134326 134581 = 19066899 := by
  decide +kernel

private theorem batch574 :
    (∑ n ∈ Finset.Icc 134326 134581, roundedTerm 10000000000 n) = 19066899 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 134326 134581 19066899
    (by decide) (by decide) weights574

private theorem weights575 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 134582 134837 = 18933434 := by
  decide +kernel

private theorem batch575 :
    (∑ n ∈ Finset.Icc 134582 134837, roundedTerm 10000000000 n) = 18933434 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 134582 134837 18933434
    (by decide) (by decide) weights575

set_option trace.profiler true in
private theorem weights576 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 134838 135093 = 18355200 := by
  decide +kernel

private theorem batch576 :
    (∑ n ∈ Finset.Icc 134838 135093, roundedTerm 10000000000 n) = 18355200 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 134838 135093 18355200
    (by decide) (by decide) weights576

private theorem weights577 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 135094 135349 = 19249998 := by
  decide +kernel

private theorem batch577 :
    (∑ n ∈ Finset.Icc 135094 135349, roundedTerm 10000000000 n) = 19249998 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 135094 135349 19249998
    (by decide) (by decide) weights577

private theorem weights578 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 135350 135605 = 18910555 := by
  decide +kernel

private theorem batch578 :
    (∑ n ∈ Finset.Icc 135350 135605, roundedTerm 10000000000 n) = 18910555 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 135350 135605 18910555
    (by decide) (by decide) weights578

private theorem weights579 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 135606 135861 = 18701596 := by
  decide +kernel

private theorem batch579 :
    (∑ n ∈ Finset.Icc 135606 135861, roundedTerm 10000000000 n) = 18701596 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 135606 135861 18701596
    (by decide) (by decide) weights579

private theorem weights580 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 135862 136117 = 19277326 := by
  decide +kernel

private theorem batch580 :
    (∑ n ∈ Finset.Icc 135862 136117, roundedTerm 10000000000 n) = 19277326 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 135862 136117 19277326
    (by decide) (by decide) weights580

private theorem weights581 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 136118 136373 = 18917027 := by
  decide +kernel

private theorem batch581 :
    (∑ n ∈ Finset.Icc 136118 136373, roundedTerm 10000000000 n) = 18917027 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 136118 136373 18917027
    (by decide) (by decide) weights581

private theorem weights582 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 136374 136629 = 18942952 := by
  decide +kernel

private theorem batch582 :
    (∑ n ∈ Finset.Icc 136374 136629, roundedTerm 10000000000 n) = 18942952 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 136374 136629 18942952
    (by decide) (by decide) weights582

private theorem weights583 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 136630 136885 = 18290094 := by
  decide +kernel

private theorem batch583 :
    (∑ n ∈ Finset.Icc 136630 136885, roundedTerm 10000000000 n) = 18290094 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 136630 136885 18290094
    (by decide) (by decide) weights583

private theorem weights584 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 136886 137141 = 18621085 := by
  decide +kernel

private theorem batch584 :
    (∑ n ∈ Finset.Icc 136886 137141, roundedTerm 10000000000 n) = 18621085 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 136886 137141 18621085
    (by decide) (by decide) weights584

private theorem weights585 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 137142 137397 = 18837059 := by
  decide +kernel

private theorem batch585 :
    (∑ n ∈ Finset.Icc 137142 137397, roundedTerm 10000000000 n) = 18837059 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 137142 137397 18837059
    (by decide) (by decide) weights585

private theorem weights586 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 137398 137653 = 18504623 := by
  decide +kernel

private theorem batch586 :
    (∑ n ∈ Finset.Icc 137398 137653, roundedTerm 10000000000 n) = 18504623 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 137398 137653 18504623
    (by decide) (by decide) weights586

private theorem weights587 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 137654 137909 = 18150648 := by
  decide +kernel

private theorem batch587 :
    (∑ n ∈ Finset.Icc 137654 137909, roundedTerm 10000000000 n) = 18150648 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 137654 137909 18150648
    (by decide) (by decide) weights587

private theorem weights588 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 137910 138165 = 19081338 := by
  decide +kernel

private theorem batch588 :
    (∑ n ∈ Finset.Icc 137910 138165, roundedTerm 10000000000 n) = 19081338 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 137910 138165 19081338
    (by decide) (by decide) weights588

private theorem weights589 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 138166 138421 = 18752260 := by
  decide +kernel

private theorem batch589 :
    (∑ n ∈ Finset.Icc 138166 138421, roundedTerm 10000000000 n) = 18752260 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 138166 138421 18752260
    (by decide) (by decide) weights589

private theorem weights590 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 138422 138677 = 18113182 := by
  decide +kernel

private theorem batch590 :
    (∑ n ∈ Finset.Icc 138422 138677, roundedTerm 10000000000 n) = 18113182 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 138422 138677 18113182
    (by decide) (by decide) weights590

private theorem weights591 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 138678 138933 = 18660965 := by
  decide +kernel

private theorem batch591 :
    (∑ n ∈ Finset.Icc 138678 138933, roundedTerm 10000000000 n) = 18660965 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 138678 138933 18660965
    (by decide) (by decide) weights591

private theorem weights592 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 138934 139189 = 18370190 := by
  decide +kernel

private theorem batch592 :
    (∑ n ∈ Finset.Icc 138934 139189, roundedTerm 10000000000 n) = 18370190 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 138934 139189 18370190
    (by decide) (by decide) weights592

private theorem weights593 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 139190 139445 = 18473716 := by
  decide +kernel

private theorem batch593 :
    (∑ n ∈ Finset.Icc 139190 139445, roundedTerm 10000000000 n) = 18473716 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 139190 139445 18473716
    (by decide) (by decide) weights593

private theorem weights594 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 139446 139545 = 7104600 := by
  decide +kernel

private theorem batch594 :
    (∑ n ∈ Finset.Icc 139446 139545, roundedTerm 10000000000 n) = 7104600 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 139446 139545 7104600
    (by decide) (by decide) weights594

private theorem weights595 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 139546 139801 = 17908123 := by
  decide +kernel

private theorem batch595 :
    (∑ n ∈ Finset.Icc 139546 139801, roundedTerm 10000000000 n) = 17908123 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 139546 139801 17908123
    (by decide) (by decide) weights595

private theorem weights596 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 139802 140057 = 18835235 := by
  decide +kernel

private theorem batch596 :
    (∑ n ∈ Finset.Icc 139802 140057, roundedTerm 10000000000 n) = 18835235 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 139802 140057 18835235
    (by decide) (by decide) weights596

private theorem weights597 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 140058 140313 = 18067301 := by
  decide +kernel

private theorem batch597 :
    (∑ n ∈ Finset.Icc 140058 140313, roundedTerm 10000000000 n) = 18067301 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 140058 140313 18067301
    (by decide) (by decide) weights597

private theorem weights598 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 140314 140569 = 18269450 := by
  decide +kernel

private theorem batch598 :
    (∑ n ∈ Finset.Icc 140314 140569, roundedTerm 10000000000 n) = 18269450 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 140314 140569 18269450
    (by decide) (by decide) weights598

private theorem weights599 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 140570 140825 = 18066321 := by
  decide +kernel

private theorem batch599 :
    (∑ n ∈ Finset.Icc 140570 140825, roundedTerm 10000000000 n) = 18066321 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 140570 140825 18066321
    (by decide) (by decide) weights599

private theorem weights600 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 140826 141081 = 18419591 := by
  decide +kernel

private theorem batch600 :
    (∑ n ∈ Finset.Icc 140826 141081, roundedTerm 10000000000 n) = 18419591 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 140826 141081 18419591
    (by decide) (by decide) weights600

private theorem weights601 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 141082 141337 = 18026282 := by
  decide +kernel

private theorem batch601 :
    (∑ n ∈ Finset.Icc 141082 141337, roundedTerm 10000000000 n) = 18026282 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 141082 141337 18026282
    (by decide) (by decide) weights601

private theorem weights602 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 141338 141593 = 18287451 := by
  decide +kernel

private theorem batch602 :
    (∑ n ∈ Finset.Icc 141338 141593, roundedTerm 10000000000 n) = 18287451 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 141338 141593 18287451
    (by decide) (by decide) weights602

private theorem weights603 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 141594 141849 = 18480821 := by
  decide +kernel

private theorem batch603 :
    (∑ n ∈ Finset.Icc 141594 141849, roundedTerm 10000000000 n) = 18480821 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 141594 141849 18480821
    (by decide) (by decide) weights603

private theorem weights604 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 141850 142105 = 18211895 := by
  decide +kernel

private theorem batch604 :
    (∑ n ∈ Finset.Icc 141850 142105, roundedTerm 10000000000 n) = 18211895 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 141850 142105 18211895
    (by decide) (by decide) weights604

private theorem weights605 :
    fastSum (boundedSquareExitRounded hybridTrial 10000000000) 142106 142300 = 13478516 := by
  decide +kernel

private theorem batch605 :
    (∑ n ∈ Finset.Icc 142106 142300, roundedTerm 10000000000 n) = 13478516 :=
  semantic_batch_of_square_exit_fast_sum 10000000000 142106 142300 13478516
    (by decide) (by decide) weights605

private theorem all_semantic_batches :
    ∀ g ∈ batchGroups, ∀ b ∈ g.batches,
      (∑ n ∈ Finset.Icc b.lo b.hi, roundedTerm 10000000000 n) = b.value := by
  exact List.forall_iff_forall_mem.mp
    ⟨
      List.forall_iff_forall_mem.mp ⟨batch361, batch362, batch363, batch364, batch365, batch366, batch367, batch368, batch369, batch370, batch371, batch372, batch373, batch374, batch375, batch376, batch377, batch378, batch379, batch380, batch381, batch382, batch383, batch384, batch385, batch386, batch387, batch388, batch389, batch390, batch391, batch392, batch393, batch394, batch395, batch396, batch397, batch398, batch399, batch400, batch401, batch402, batch403, batch404, batch405, batch406, batch407⟩,
      List.forall_iff_forall_mem.mp ⟨batch408, batch409, batch410, batch411, batch412, batch413, batch414, batch415, batch416, batch417, batch418, batch419, batch420, batch421, batch422, batch423, batch424, batch425, batch426, batch427, batch428, batch429, batch430, batch431, batch432, batch433, batch434, batch435, batch436, batch437, batch438, batch439, batch440, batch441, batch442, batch443, batch444, batch445, batch446, batch447, batch448, batch449, batch450, batch451, batch452, batch453, batch454, batch455, batch456, batch457, batch458, batch459, batch460, batch461⟩,
      List.forall_iff_forall_mem.mp ⟨batch462, batch463, batch464, batch465, batch466, batch467, batch468, batch469, batch470, batch471, batch472, batch473, batch474, batch475, batch476, batch477, batch478, batch479, batch480, batch481, batch482, batch483, batch484, batch485, batch486, batch487, batch488, batch489, batch490, batch491, batch492, batch493, batch494, batch495, batch496, batch497, batch498, batch499, batch500, batch501, batch502, batch503, batch504, batch505, batch506, batch507, batch508, batch509, batch510, batch511, batch512, batch513, batch514, batch515, batch516, batch517, batch518, batch519, batch520, batch521, batch522, batch523⟩,
      List.forall_iff_forall_mem.mp ⟨batch524, batch525, batch526, batch527, batch528, batch529, batch530, batch531, batch532, batch533, batch534, batch535, batch536, batch537, batch538, batch539, batch540, batch541, batch542, batch543, batch544, batch545, batch546, batch547, batch548, batch549, batch550, batch551, batch552, batch553, batch554, batch555, batch556, batch557, batch558, batch559, batch560, batch561, batch562, batch563, batch564, batch565, batch566, batch567, batch568, batch569, batch570, batch571, batch572, batch573, batch574, batch575, batch576, batch577, batch578, batch579, batch580, batch581, batch582, batch583, batch584, batch585, batch586, batch587, batch588, batch589, batch590, batch591, batch592, batch593, batch594⟩,
      List.forall_iff_forall_mem.mp ⟨batch595, batch596, batch597, batch598, batch599, batch600, batch601, batch602, batch603, batch604, batch605⟩
    ⟩

/-- Exact prefix totals on the selected public endpoint range. -/
private theorem endpoint_prefixes_range (hcut : RamareFiniteBounds.roundedPrefix 10000000000 80257 = 126251687858) :
    ∀ e ∈ RamareFiniteBounds.logEndpoints, 80257 < e.hi →
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper := by
  have hprefix : (∑ n ∈ Finset.Ico 1 (80257 + 1),
      roundedTerm 10000000000 n) = 126251687858 := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    exact hcut
  have hall := batchGroupsCheck_sound (roundedTerm 10000000000) batchGroups 80258 126251687858
    (by decide) hprefix batchGroups_checked all_semantic_batches
  intro e he hrange
  have hm : e ∈ batchGroups.map EndpointBatchGroup.endpoint := by
    rw [batchGroups_endpoints]
    simpa only [List.mem_filter, decide_eq_true_eq] using (And.intro he hrange)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
  exact hall g hg

end RamareFiniteBoundsArithmetic

theorem solution (hcut : RamareFiniteBounds.roundedPrefix 10000000000 80257 = 126251687858) :
    ∀ e ∈ RamareFiniteBounds.logEndpoints, 80257 < e.hi →
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper :=
  RamareFiniteBoundsArithmetic.endpoint_prefixes_range hcut

#print axioms solution
