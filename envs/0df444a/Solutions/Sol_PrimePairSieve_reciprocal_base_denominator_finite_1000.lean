-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_1000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:48:16.767804+00:00
-- url     : https://prove2.me/submissions/7157514d-3297-4d8b-9bc9-f3376a2586a8

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries

set_option autoImplicit false

namespace PPS1151

open TaoFivePrimes

/-! ## Part 1: a lower bound for the twin prime constant -/

noncomputable def fac (p : ℕ) : ℝ := if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

lemma partial_eq (Q : ℕ) : twinPrimePartial Q = ∏ p ∈ Finset.range (Q + 1), fac p := rfl

lemma partial_succ (Q : ℕ) : twinPrimePartial (Q + 1) = twinPrimePartial Q * fac (Q + 1) := by
  rw [partial_eq, partial_eq, Finset.prod_range_succ]

lemma fac_le_one (p : ℕ) : fac p ≤ 1 := by
  unfold fac
  split_ifs
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

lemma fac_nonneg (p : ℕ) : 0 ≤ fac p := by
  unfold fac
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.2
    have h4 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := (div_le_one (lt_of_lt_of_le one_pos h4)).2 h4
    linarith
  · exact zero_le_one

lemma partial_nonneg (Q : ℕ) : 0 ≤ twinPrimePartial Q := by
  rw [partial_eq]; exact Finset.prod_nonneg (fun p _ => fac_nonneg p)

lemma fac_ge (Q : ℕ) (hQ : 2 ≤ Q) : 1 - 1 / (Q : ℝ) ^ 2 ≤ fac (Q + 1) := by
  unfold fac
  split_ifs
  · have : ((Q + 1 : ℕ) : ℝ) - 1 = Q := by push_cast; ring
    rw [this]
  · have : 0 ≤ 1 / (Q : ℝ) ^ 2 := by positivity
    linarith

lemma partial_base : (13 / 20 : ℝ) * 52 ≤ twinPrimePartial 52 * (52 - 1) := by
  rw [partial_eq]
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, fac]
  norm_num

lemma partial_aux (n : ℕ) :
    (13 / 20 : ℝ) * ((52 + n : ℕ) : ℝ) ≤ twinPrimePartial (52 + n) * (((52 + n : ℕ) : ℝ) - 1) := by
  induction n with
  | zero => simpa using partial_base
  | succ n ih =>
    rw [show 52 + (n + 1) = (52 + n) + 1 by ring, partial_succ]
    set Q : ℕ := 52 + n with hQdef
    have hQ2 : 2 ≤ Q := by omega
    have hQr : (52 : ℝ) ≤ Q := by rw [hQdef]; push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hQ0 : (0 : ℝ) < Q := by linarith
    set a := twinPrimePartial Q
    have ha : 0 ≤ a := partial_nonneg Q
    have hf := fac_ge Q hQ2
    rw [show ((Q + 1 : ℕ) : ℝ) = (Q : ℝ) + 1 by push_cast; ring, add_sub_cancel_right]
    have hQne : (Q : ℝ) ≠ 0 := hQ0.ne'
    have e : a * (1 - 1 / (Q : ℝ) ^ 2) * Q * Q = a * ((Q : ℝ) - 1) * ((Q : ℝ) + 1) := by
      field_simp
      ring
    have h1 : a * (1 - 1 / (Q : ℝ) ^ 2) * Q ≤ a * fac (Q + 1) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf ha) hQ0.le
    have h2 : (13 / 20 : ℝ) * ((Q : ℝ) + 1) * Q ≤ a * (1 - 1 / (Q : ℝ) ^ 2) * Q * Q := by
      rw [e]
      have := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ Q + 1)
      linarith
    have h3 : (13 / 20 : ℝ) * ((Q : ℝ) + 1) ≤ a * (1 - 1 / (Q : ℝ) ^ 2) * Q :=
      le_of_mul_le_mul_right h2 hQ0
    linarith

lemma partial_anti : Antitone twinPrimePartial :=
  antitone_nat_of_succ_le (fun n => by
    rw [partial_succ]; exact mul_le_of_le_one_right (partial_nonneg n) (fac_le_one _))

lemma partial_lb (Q : ℕ) : (13 / 20 : ℝ) ≤ twinPrimePartial Q := by
  have key : ∀ n : ℕ, (13 / 20 : ℝ) ≤ twinPrimePartial (52 + n) := by
    intro n
    have h := partial_aux n
    have hQ : (52 : ℝ) ≤ ((52 + n : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have ha := partial_nonneg (52 + n)
    rcases lt_or_ge (twinPrimePartial (52 + n)) (13 / 20) with hc | hc
    · nlinarith
    · exact hc
  by_cases hQ : 52 ≤ Q
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hQ
    exact key n
  · have := key 0
    simp only [add_zero] at this
    exact this.trans (partial_anti (by omega))

lemma twin_lb : (13 / 10 : ℝ) ≤ twinPrimeConstant := by
  unfold twinPrimeConstant
  have : (13 / 20 : ℝ) ≤ sInf (Set.range twinPrimePartial) :=
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨Q, rfl⟩; exact partial_lb Q)
  linarith

/-! ## Part 2: logarithm upper bounds -/

lemma log_bound (x y a : ℝ) (k n : ℕ) (hx : x = 2 ^ k * (1 + y)) (hya : |y| ≤ a) (ha : a < 1) :
    Real.log x ≤ k * 0.6931471808 +
      (-(∑ i ∈ Finset.range n, (-y) ^ (i + 1) / (i + 1)) + a ^ (n + 1) / (1 - a)) := by
  have hy : |y| < 1 := lt_of_le_of_lt hya ha
  have h1 : 0 < 1 + y := by linarith [neg_abs_le y]
  rw [hx, Real.log_mul (by positivity) h1.ne', Real.log_pow]
  have h2 := Real.abs_log_sub_add_sum_range_le (x := -y) (by rwa [abs_neg]) n
  rw [abs_neg, sub_neg_eq_add] at h2
  have h3 := (abs_le.1 h2).2
  have h4 := Real.log_two_lt_d9
  have h5 : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left h4.le (Nat.cast_nonneg k)
  have h6 : |y| ^ (n + 1) / (1 - |y|) ≤ a ^ (n + 1) / (1 - a) :=
    div_le_div₀ (by have := (abs_nonneg y).trans hya; positivity)
      (pow_le_pow_left₀ (abs_nonneg y) hya _) (by linarith) (by linarith)
  linarith

/-! ## Part 3: the weight table -/

def fQ (p : ℕ) : ℚ := if p = 2 then 1 else 2 / ((p : ℚ) - 2)

def termQ (L : ℕ) (l : List ℕ) : ℚ := (l.map fQ).prod / (1 + (l.prod : ℚ) / L)

def sumQ (L : ℕ) (T : List (List ℕ)) : ℚ := ((T.filter (fun l => l.prod ≤ L)).map (termQ L)).sum

noncomputable def fR (p : ℕ) : ℝ := if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)

noncomputable def wR (n : ℕ) : ℝ := if Squarefree n then ∏ p ∈ n.primeFactors, fR p else 0

lemma cast_fQ (p : ℕ) : ((fQ p : ℚ) : ℝ) = fR p := by
  unfold fQ fR; split_ifs <;> simp

lemma fR_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ fR p := by
  unfold fR
  split_ifs with h
  · exact zero_le_one
  · have h3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm h))
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    exact div_nonneg (by norm_num) (by linarith)

lemma wR_nonneg (n : ℕ) : 0 ≤ wR n := by
  unfold wR
  split_ifs
  · exact Finset.prod_nonneg (fun p hp => fR_nonneg p (Nat.prime_of_mem_primeFactors hp))
  · exact le_rfl

lemma wR_list (l : List ℕ) (hs : l.Pairwise (· < ·)) (hp : ∀ p ∈ l, p.Prime) :
    wR l.prod = (l.map fR).prod := by
  have hnd : l.Nodup := hs.imp (fun h => h.ne)
  have hperm := Nat.primeFactorsList_unique rfl hp
  have h0 : l.prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]; intro h; exact Nat.not_prime_zero (hp 0 h)
  have hsq : Squarefree l.prod :=
    (Nat.squarefree_iff_nodup_primeFactorsList h0).2 (hperm.nodup_iff.1 hnd)
  have hpf : l.prod.primeFactors = l.toFinset := by
    rw [← Nat.toFinset_factors]; exact (List.toFinset_eq_of_perm _ _ hperm).symm
  rw [wR, if_pos hsq, hpf, List.prod_toFinset _ hnd]

def P : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

set_option maxRecDepth 100000 in
lemma hP_check : ∀ p ∈ P, 2 ≤ p ∧ ∀ d ∈ List.range p, 2 ≤ d → p % d ≠ 0 := by
  decide +kernel

lemma hP : ∀ p ∈ P, p.Prime := by
  intro p hp
  obtain ⟨h2, h⟩ := hP_check p hp
  refine Nat.prime_def_lt'.2 ⟨h2, fun m hm hmp hdvd => ?_⟩
  exact h m (List.mem_range.2 hmp) hm (Nat.mod_eq_zero_of_dvd hdvd)

def T0 : List (List ℕ) := [[], [2], [3], [5], [2, 3], [7], [2, 5], [11], [13], [2, 7], [3, 5], [17], [19], [3, 7], [2, 11], [23], [2, 13], [29], [2, 3, 5], [31], [3, 11], [2, 17], [5, 7], [37], [2, 19], [3, 13], [41], [2, 3, 7], [43], [2, 23], [47], [3, 17], [53], [5, 11], [3, 19], [2, 29], [59], [61], [2, 31], [5, 13], [2, 3, 11], [67], [3, 23], [2, 5, 7], [71], [73], [2, 37], [7, 11], [2, 3, 13], [79], [2, 41], [83], [5, 17], [2, 43], [3, 29], [89], [7, 13], [3, 31], [2, 47], [5, 19], [97], [101], [2, 3, 17], [103], [3, 5, 7], [2, 53], [107], [109], [2, 5, 11], [3, 37], [113], [2, 3, 19], [5, 23], [2, 59], [7, 17], [2, 61], [3, 41], [127], [3, 43], [2, 5, 13], [131], [7, 19], [2, 67], [137], [2, 3, 23], [139], [3, 47], [2, 71], [11, 13], [5, 29], [2, 73], [149], [151], [2, 7, 11], [5, 31], [157], [2, 79], [3, 53], [7, 23], [163]]
def T1 : List (List ℕ) := [[3, 5, 11], [2, 83], [167], [2, 5, 17], [173], [2, 3, 29], [3, 59], [2, 89], [179], [181], [2, 7, 13], [3, 61], [5, 37], [2, 3, 31], [11, 17], [2, 5, 19], [191], [193], [2, 97], [3, 5, 13], [197], [199], [3, 67], [2, 101], [7, 29], [5, 41], [2, 103], [11, 19], [2, 3, 5, 7], [211], [3, 71], [2, 107], [5, 43], [7, 31], [2, 109], [3, 73], [13, 17], [2, 3, 37], [223], [2, 113], [227], [229], [2, 5, 23], [3, 7, 11], [233], [5, 47], [3, 79], [2, 7, 17], [239], [241], [2, 3, 41], [13, 19], [3, 83], [251], [11, 23], [2, 127], [3, 5, 17], [257], [2, 3, 43], [7, 37], [2, 131], [263], [5, 53], [2, 7, 19], [3, 89], [269], [271], [3, 7, 13], [2, 137], [277], [2, 139], [281], [2, 3, 47], [283], [3, 5, 19], [2, 11, 13], [7, 41], [2, 5, 29], [3, 97], [293], [5, 59], [2, 149], [13, 23], [7, 43], [2, 151], [3, 101], [5, 61], [307], [3, 103], [2, 5, 31], [311], [313], [2, 157], [317], [2, 3, 53], [11, 29], [3, 107], [2, 7, 23], [17, 19], [2, 163]]
def T2 : List (List ℕ) := [[3, 109], [7, 47], [2, 3, 5, 11], [331], [2, 167], [5, 67], [337], [3, 113], [11, 31], [3, 5, 23], [2, 173], [347], [349], [353], [2, 3, 59], [5, 71], [3, 7, 17], [2, 179], [359], [2, 181], [5, 73], [2, 3, 61], [367], [2, 5, 37], [7, 53], [373], [2, 11, 17], [13, 29], [379], [3, 127], [2, 191], [383], [5, 7, 11], [2, 193], [389], [2, 3, 5, 13], [17, 23], [3, 131], [2, 197], [5, 79], [397], [2, 199], [3, 7, 19], [401], [2, 3, 67], [13, 31], [2, 7, 29], [11, 37], [409], [2, 5, 41], [3, 137], [7, 59], [5, 83], [3, 139], [2, 11, 19], [419], [421], [2, 211], [2, 3, 71], [7, 61], [3, 11, 13], [2, 5, 43], [431], [433], [2, 7, 31], [3, 5, 29], [19, 23], [2, 3, 73], [439], [2, 13, 17], [443], [5, 89], [2, 223], [3, 149], [449], [11, 41], [3, 151], [2, 227], [5, 7, 13], [457], [2, 229], [461], [2, 3, 7, 11], [463], [3, 5, 31], [2, 233], [467], [7, 67], [2, 5, 47], [3, 157], [11, 43], [2, 3, 79], [2, 239], [479], [13, 37], [2, 241], [3, 7, 23], [5, 97], [487], [3, 163]]
def T3 : List (List ℕ) := [[491], [17, 29], [2, 13, 19], [7, 71], [2, 3, 83], [499], [3, 167], [2, 251], [503], [5, 101], [2, 11, 23], [509], [2, 3, 5, 17], [7, 73], [2, 257], [5, 103], [11, 47], [2, 7, 37], [3, 173], [521], [523], [2, 263], [17, 31], [2, 5, 53], [13, 41], [2, 3, 89], [5, 107], [3, 179], [2, 269], [541], [2, 271], [3, 181], [5, 109], [2, 3, 7, 13], [547], [19, 29], [7, 79], [2, 277], [3, 5, 37], [557], [13, 43], [3, 11, 17], [2, 281], [563], [5, 113], [2, 283], [569], [2, 3, 5, 19], [571], [3, 191], [2, 7, 41], [577], [3, 193], [7, 83], [2, 3, 97], [11, 53], [2, 293], [587], [19, 31], [2, 5, 59], [3, 197], [593], [5, 7, 17], [3, 199], [2, 13, 23], [599], [601], [2, 7, 43], [2, 3, 101], [607], [3, 7, 29], [2, 5, 61], [13, 47], [613], [2, 307], [3, 5, 41], [617], [2, 3, 103], [619], [2, 311], [7, 89], [2, 313], [3, 11, 19], [17, 37], [631], [3, 211], [2, 317], [5, 127], [2, 11, 29], [641], [2, 3, 107], [643], [3, 5, 43], [2, 17, 19], [647], [11, 59], [3, 7, 31], [653], [2, 3, 109], [5, 131]]
def T4 : List (List ℕ) := [[2, 7, 47], [659], [661], [2, 331], [3, 13, 17], [5, 7, 19], [23, 29], [3, 223], [2, 5, 67], [11, 61], [673], [2, 337], [677], [2, 3, 113], [7, 97], [3, 227], [2, 11, 31], [683], [5, 137], [3, 229], [13, 53], [2, 3, 5, 23], [691], [2, 347], [5, 139], [17, 41], [2, 349], [3, 233], [701], [19, 37], [3, 5, 47], [2, 353], [7, 101], [709], [2, 5, 71], [23, 31], [2, 3, 7, 17], [5, 11, 13], [3, 239], [2, 359], [719], [7, 103], [3, 241], [727], [2, 5, 73], [17, 43], [733], [2, 367], [11, 67], [739], [3, 13, 19], [2, 7, 53], [743], [5, 149], [2, 373], [7, 107], [751], [3, 251], [2, 13, 29], [5, 151], [757], [2, 379], [3, 11, 23], [761], [2, 3, 127], [7, 109], [2, 383], [13, 59], [769], [2, 5, 7, 11], [3, 257], [773], [3, 7, 37], [2, 389], [19, 41], [11, 71], [2, 17, 23], [5, 157], [2, 3, 131], [787], [3, 263], [2, 5, 79], [7, 113], [13, 61], [2, 397], [3, 5, 53], [797], [2, 3, 7, 19], [17, 47], [2, 401], [11, 73], [5, 7, 23], [2, 13, 31], [3, 269], [809], [811], [3, 271], [2, 11, 37], [5, 163], [19, 43]]
def T5 : List (List ℕ) := [[2, 409], [821], [2, 3, 137], [823], [2, 7, 59], [827], [829], [2, 5, 83], [3, 277], [2, 3, 139], [5, 167], [2, 419], [839], [2, 421], [3, 281], [3, 283], [23, 37], [853], [2, 7, 61], [857], [2, 3, 11, 13], [859], [3, 7, 41], [2, 431], [863], [5, 173], [2, 433], [11, 79], [2, 3, 5, 29], [13, 67], [2, 19, 23], [877], [2, 439], [3, 293], [881], [883], [3, 5, 59], [2, 443], [887], [7, 127], [2, 5, 89], [19, 47], [2, 3, 149], [5, 179], [3, 13, 23], [2, 449], [29, 31], [17, 53], [2, 11, 41], [3, 7, 43], [5, 181], [2, 3, 151], [907], [2, 5, 7, 13], [911], [11, 83], [2, 457], [3, 5, 61], [7, 131], [919], [3, 307], [2, 461], [13, 71], [2, 463], [929], [2, 3, 5, 31], [3, 311], [2, 467], [5, 11, 17], [937], [2, 7, 67], [3, 313], [941], [2, 3, 157], [23, 41], [2, 11, 43], [947], [13, 73], [3, 317], [953], [5, 191], [3, 11, 29], [2, 479], [7, 137], [2, 13, 37], [5, 193], [2, 3, 7, 23], [967], [3, 17, 19], [2, 5, 97], [971], [7, 139], [2, 487], [977], [2, 3, 163], [11, 89], [2, 491], [983], [5, 197], [2, 17, 29]]
def T6 : List (List ℕ) := [[3, 7, 47], [23, 43], [991], [3, 331], [2, 7, 71], [5, 199], [997], [2, 499]]
def T : List (List ℕ) := T0 ++ T1 ++ T2 ++ T3 ++ T4 ++ T5 ++ T6

set_option maxRecDepth 100000 in
lemma hT : (∀ l ∈ T, l.Pairwise (· < ·) ∧ ∀ p ∈ l, p ∈ P) ∧ (T.map List.prod).IsChain (· < ·) := by
  decide +kernel

lemma table_le (L : ℕ) :
    ((sumQ L T : ℚ) : ℝ) ≤ ∑ q ∈ Finset.Icc 1 L, wR q / (1 + (q : ℝ) / L) := by
  set T' := T.filter (fun l => l.prod ≤ L) with hT'
  have hpw : (T'.map List.prod).Pairwise (· < ·) :=
    (List.isChain_iff_pairwise.1 hT.2).sublist ((List.filter_sublist ..).map List.prod)
  have hnd : (T'.map List.prod).Nodup := hpw.imp (fun h => h.ne)
  have hmem : ∀ l ∈ T', (∀ p ∈ l, p.Prime) ∧ l.Pairwise (· < ·) ∧ l.prod ≤ L := by
    intro l hl
    rw [hT', List.mem_filter] at hl
    exact ⟨fun p hp => hP p ((hT.1 l hl.1).2 p hp), (hT.1 l hl.1).1, by simpa using hl.2⟩
  have hsub : (T'.map List.prod).toFinset ⊆ Finset.Icc 1 L := by
    intro q hq
    rw [List.mem_toFinset, List.mem_map] at hq
    obtain ⟨l, hl, rfl⟩ := hq
    obtain ⟨h1, -, h3⟩ := hmem l hl
    rw [Finset.mem_Icc]
    exact ⟨List.prod_pos (fun p hp => (h1 p hp).pos), h3⟩
  calc ((sumQ L T : ℚ) : ℝ)
        = ∑ q ∈ (T'.map List.prod).toFinset, wR q / (1 + (q : ℝ) / L) := by
        rw [List.sum_toFinset _ hnd, List.map_map, sumQ, Rat.cast_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro l hl
        obtain ⟨h1, h2, -⟩ := hmem l hl
        simp only [Function.comp_apply, termQ, Rat.cast_div, Rat.cast_add, Rat.cast_one,
          Rat.cast_natCast, Rat.cast_list_prod, List.map_map, Function.comp_def, cast_fQ]
        rw [wR_list l h2 h1]
    _ ≤ ∑ q ∈ Finset.Icc 1 L, wR q / (1 + (q : ℝ) / L) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun q _ _ => div_nonneg (wR_nonneg q) (by positivity))

lemma sum_mono (z : ℝ) (L : ℕ) (hL : (L : ℝ) ≤ z) (hL1 : 1 ≤ L) :
    ∑ q ∈ Finset.Icc 1 L, wR q / (1 + (q : ℝ) / L) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊, wR q / (1 + (q : ℝ) / z) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hz0 : 0 < z := lt_of_lt_of_le hL0 hL
  calc ∑ q ∈ Finset.Icc 1 L, wR q / (1 + (q : ℝ) / L)
        ≤ ∑ q ∈ Finset.Icc 1 L, wR q / (1 + (q : ℝ) / z) := by
        apply Finset.sum_le_sum
        intro q _
        apply div_le_div_of_nonneg_left (wR_nonneg q) (by positivity)
        have : (q : ℝ) / z ≤ q / L := div_le_div_of_nonneg_left (Nat.cast_nonneg q) hL0 hL
        linarith
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊, wR q / (1 + (q : ℝ) / z) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.le_floor hL))
          (fun q _ _ => div_nonneg (wR_nonneg q) (by positivity))

/-! ## Part 4: one cell -/

def Stmt (z : ℝ) : Prop :=
      Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/z)

lemma cell (z : ℝ) (L : ℕ) (U ell s : ℝ) (hL40 : 40 ≤ L) (hLz : (L : ℝ) ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4 * U) ≤ ell) (hs : s ≤ ((sumQ L T : ℚ) : ℝ))
    (hpos : ((L : ℝ) + 1) / (16 * (L : ℝ) ^ 2) * (ell ^ 2 / (13 / 5)) < 1)
    (hcert : ell ^ 2 / (13 / 5) / (1 - ((L : ℝ) + 1) / (16 * (L : ℝ) ^ 2) * (ell ^ 2 / (13 / 5))) ≤ s) :
    Stmt z := by
  have hL0 : (40 : ℝ) ≤ L := by exact_mod_cast hL40
  have hz0 : 0 < z := by linarith
  have hC := twin_lb
  have hlogz0 : 0 ≤ Real.log (4 * z) := Real.log_nonneg (by linarith)
  have hlogz : Real.log (4 * z) ≤ ell := le_trans (Real.log_le_log (by linarith) (by linarith)) hlog
  have hRHS : s ≤ ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, wR n / (1 + (n : ℝ) / z) :=
    hs.trans ((table_le L).trans (sum_mono z L hLz (by omega)))
  unfold Stmt
  show _ ≤ ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, wR n / (1 + (n : ℝ) / z)
  refine le_trans ?_ (hcert.trans hRHS)
  set C := TaoFivePrimes.twinPrimeConstant
  set A := Real.log (4 * z) ^ 2 / (2 * C) with hA
  set B := ell ^ 2 / (13 / 5) with hB
  set c := ((L : ℝ) + 1) / (16 * (L : ℝ) ^ 2) with hc
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg _) (by linarith)
  have hB0 : 0 ≤ B := div_nonneg (sq_nonneg _) (by norm_num)
  have hAB : A ≤ B := by
    calc A ≤ ell ^ 2 / (2 * C) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogz0 hlogz 2) (by linarith)
      _ ≤ B := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcz : (z + 1) / (16 * z ^ 2) ≤ c := by
    rw [hc, div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hz0 2)) (mul_pos (by norm_num) (pow_pos (by linarith) 2))]
    have h1 : 0 ≤ (L : ℝ) * z * (z - L) := by
      apply mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (z - L) * (z + L) := by
      apply mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : (z + 1) * A / (16 * z ^ 2) ≤ c * B := by
    rw [show (z + 1) * A / (16 * z ^ 2) = (z + 1) / (16 * z ^ 2) * A by ring]
    exact mul_le_mul hcz hAB hA0 hc0
  have hpos' : 0 < 1 - c * B := by linarith
  exact div_le_div₀ hB0 hAB hpos' (by linarith)


set_option maxRecDepth 100000 in
lemma sum_40 : (11159/1000 : ℚ) ≤ sumQ 40 T := by
  decide +kernel

lemma cell_40 (z : ℝ) (h1 : (40 : ℝ) ≤ z) (h2 : z ≤ 52) : Stmt z := by
  refine cell z 40 52 (53375381/10000000) ((11159/1000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 52) (-3/16) (3/16) 8 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_40
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_52 : (24781/2000 : ℚ) ≤ sumQ 52 T := by
  decide +kernel

lemma cell_52 (z : ℝ) (h1 : (52 : ℝ) ≤ z) (h2 : z ≤ 69) : Stmt z := by
  refine cell z 52 69 (562040087/100000000) ((24781/2000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 69) (5/64) (5/64) 8 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_52
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_69 : (137233/10000 : ℚ) ≤ sumQ 69 T := by
  decide +kernel

lemma cell_69 (z : ℝ) (h1 : (69 : ℝ) ≤ z) (h2 : z ≤ 94) : Stmt z := by
  refine cell z 69 94 (74119873/12500000) ((137233/10000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 94) (-17/64) (17/64) 9 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_69
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_94 : (18987/1250 : ℚ) ≤ sumQ 94 T := by
  decide +kernel

lemma cell_94 (z : ℝ) (h1 : (94 : ℝ) ≤ z) (h2 : z ≤ 129) : Stmt z := by
  refine cell z 94 129 (624610677/100000000) ((18987/1250 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 129) (1/128) (1/128) 9 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_94
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_129 : (8461/500 : ℚ) ≤ sumQ 129 T := by
  decide +kernel

lemma cell_129 (z : ℝ) (h1 : (129 : ℝ) ≤ z) (h2 : z ≤ 184) : Stmt z := by
  refine cell z 129 184 (82515393/12500000) ((8461/500 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 184) (-9/32) (9/32) 10 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_129
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_184 : (187231/10000 : ℚ) ≤ sumQ 184 T := by
  decide +kernel

lemma cell_184 (z : ℝ) (h1 : (184 : ℝ) ≤ z) (h2 : z ≤ 262) : Stmt z := by
  refine cell z 184 262 (695463887/100000000) ((187231/10000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 262) (3/128) (3/128) 10 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_184
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_262 : (41983/2000 : ℚ) ≤ sumQ 262 T := by
  decide +kernel

lemma cell_262 (z : ℝ) (h1 : (262 : ℝ) ≤ z) (h2 : z ≤ 396) : Stmt z := by
  refine cell z 262 396 (736770869/100000000) ((41983/2000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 396) (-29/128) (29/128) 11 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_262
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_396 : (234921/10000 : ℚ) ≤ sumQ 396 T := by
  decide +kernel

lemma cell_396 (z : ℝ) (h1 : (396 : ℝ) ≤ z) (h2 : z ≤ 610) : Stmt z := by
  refine cell z 396 610 (389987667/50000000) ((234921/10000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 610) (49/256) (49/256) 11 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_396
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_610 : (263517/10000 : ℚ) ≤ sumQ 610 T := by
  decide +kernel

lemma cell_610 (z : ℝ) (h1 : (610 : ℝ) ≤ z) (h2 : z ≤ 972) : Stmt z := by
  refine cell z 610 972 (826565017/100000000) ((263517/10000 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 972) (-13/256) (13/256) 12 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_610
  · norm_num
  · norm_num


set_option maxRecDepth 100000 in
lemma sum_972 : (18437/625 : ℚ) ≤ sumQ 972 T := by
  decide +kernel

lemma cell_972 (z : ℝ) (h1 : (972 : ℝ) ≤ z) (h2 : z ≤ 1000) : Stmt z := by
  refine cell z 972 1000 (165880993/20000000) ((18437/625 : ℚ) : ℝ) (by norm_num) (by simpa using h1) h2 ?_ ?_ ?_ ?_
  · refine (log_bound (4 * 1000) (-3/128) (3/128) 12 10 (by norm_num) ?_ (by norm_num)).trans ?_
    · rw [abs_le]; constructor <;> norm_num
    · norm_num [Finset.sum_range_succ]
  · exact Rat.cast_le.2 sum_972
  · norm_num
  · norm_num

end PPS1151

theorem solution (z : ℝ) (hz : 40 ≤ z) (hupper : z ≤ 1000) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/z) := by
  rcases le_or_gt z 52 with h0 | h0
  · exact PPS1151.cell_40 z hz h0
  rcases le_or_gt z 69 with h1 | h1
  · exact PPS1151.cell_52 z h0.le h1
  rcases le_or_gt z 94 with h2 | h2
  · exact PPS1151.cell_69 z h1.le h2
  rcases le_or_gt z 129 with h3 | h3
  · exact PPS1151.cell_94 z h2.le h3
  rcases le_or_gt z 184 with h4 | h4
  · exact PPS1151.cell_129 z h3.le h4
  rcases le_or_gt z 262 with h5 | h5
  · exact PPS1151.cell_184 z h4.le h5
  rcases le_or_gt z 396 with h6 | h6
  · exact PPS1151.cell_262 z h5.le h6
  rcases le_or_gt z 610 with h7 | h7
  · exact PPS1151.cell_396 z h6.le h7
  rcases le_or_gt z 972 with h8 | h8
  · exact PPS1151.cell_610 z h7.le h8
  exact PPS1151.cell_972 z h8.le hupper
