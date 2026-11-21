-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.Supplement.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:58:16.295178+00:00
-- url     : https://prove2.me/submissions/7defff21-1e0e-4422-8a02-553c0c4b9f4e

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_BinomialRatio

section
set_option autoImplicit false

namespace RandOnlineSetCoverSqrt.Dev.L64
open RandOnlineSetCoverSqrt.LowerBound.Supplement Finset

/-- The base `b = exp(-α H(1/α))`. -/
noncomputable def bb (α : ℝ) : ℝ := Real.exp (-(α * Real.binEntropy (1 / α)))

lemma bb_pos (α : ℝ) : 0 < bb α := Real.exp_pos _

/-- One term of a binomial expansion is at most the whole sum. -/
lemma binom_term_le (n k : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hkn : k ≤ n) :
    (n.choose k : ℝ) * x ^ k * y ^ (n - k) ≤ (x + y) ^ n := by
  rw [add_pow]
  have hmem : k ∈ range (n + 1) := mem_range.mpr (by omega)
  refine le_trans (le_of_eq (by ring)) (single_le_sum (f := fun j => x ^ j * y ^ (n - j) * (n.choose j : ℝ))
    (fun j _ => by positivity) hmem)

/-- The mode of a binomial distribution carries at least `1/(n+1)` of the mass. -/
lemma binom_mode (n k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h1 : (k : ℝ) ≤ ((n : ℝ) + 1) * p) (h2 : ((n : ℝ) + 1) * p ≤ (k : ℝ) + 1) :
    1 ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
  set t : ℕ → ℝ := fun j => (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) with ht
  have hq : 0 < 1 - p := by linarith
  have ht0 : ∀ j, 0 ≤ t j := fun j => by simp only [ht]; positivity
  have hstep : ∀ j, j < n → t (j + 1) * (((j : ℝ) + 1) * (1 - p)) = t j * (((n - j : ℕ) : ℝ) * p) := by
    intro j hj
    have hc : ((n.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) = (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq n j
    have hpow : (1 - p) ^ (n - j) = (1 - p) ^ (n - (j + 1)) * (1 - p) := by
      rw [← pow_succ]; congr 1; omega
    simp only [ht]
    rw [hpow]
    linear_combination (p ^ (j + 1) * (1 - p) ^ (n - (j + 1)) * (1 - p)) * hc
  have hdec : ∀ j, k ≤ j → j < n → t (j + 1) ≤ t j := by
    intro j hkj hj
    have hpos : 0 < ((j : ℝ) + 1) * (1 - p) := by positivity
    have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have hcmp : ((n - j : ℕ) : ℝ) * p ≤ ((j : ℝ) + 1) * (1 - p) := by
      rw [Nat.cast_sub hj.le]; nlinarith
    have h := hstep j hj
    refine le_of_mul_le_mul_right ?_ hpos
    rw [h]; exact mul_le_mul_of_nonneg_left hcmp (ht0 j)
  have hinc : ∀ j, j + 1 ≤ k → j < n → t j ≤ t (j + 1) := by
    intro j hjk hj
    have hpos : 0 < ((j : ℝ) + 1) * (1 - p) := by positivity
    have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hcmp : ((j : ℝ) + 1) * (1 - p) ≤ ((n - j : ℕ) : ℝ) * p := by
      rw [Nat.cast_sub hj.le]; nlinarith
    have h := hstep j hj
    refine le_of_mul_le_mul_right ?_ hpos
    rw [h]; exact mul_le_mul_of_nonneg_left hcmp (ht0 j)
  have hkn : k ≤ n := by
    by_contra hcon
    have : (n : ℝ) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    nlinarith
  have hmax : ∀ j, j ≤ n → t j ≤ t k := by
    intro j hjn
    rcases le_total k j with h | h
    · induction j, h using Nat.le_induction with
      | base => exact le_rfl
      | succ i hki ih => exact (hdec i hki (by omega)).trans (ih (by omega))
    · have key : ∀ d j, j + d = k → t j ≤ t k := by
        intro d
        induction d with
        | zero => intro j hj; simp at hj; rw [hj]
        | succ d ih => intro j hj; exact (hinc j (by omega) (by omega)).trans (ih (j + 1) (by omega))
      exact key (k - j) j (by omega)
  have hsum : ∑ j ∈ range (n + 1), t j = 1 := by
    have h : (p + (1 - p)) ^ n = 1 := by norm_num
    rw [add_pow] at h
    rw [← h]; apply sum_congr rfl; intro j _; simp only [ht]; ring
  have hle : ∑ j ∈ range (n + 1), t j ≤ ∑ _j ∈ range (n + 1), t k :=
    sum_le_sum (fun j hj => hmax j (by have := mem_range.mp hj; omega))
  rw [hsum, sum_const, card_range, nsmul_eq_mul] at hle
  push_cast at hle
  simpa [ht] using hle

/-- For `α > 1` and `k ≤ r`: `b^k = p^k q^(r-k) exp((αk - r) log q)` with `p = 1/α`, `q = 1 - p`. -/
lemma bb_pow (α : ℝ) (hα : 1 < α) (k r : ℕ) (hkr : k ≤ r) :
    bb α ^ k = (1 / α) ^ k * (1 - 1 / α) ^ (r - k) *
      Real.exp ((α * k - r) * Real.log (1 - 1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hp : 0 < 1 / α := by positivity
  have hq : 0 < 1 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hαp : α * (1 / α) = 1 := by field_simp
  have hH : α * Real.binEntropy (1 / α) =
      -Real.log (1 / α) - (α - 1) * Real.log (1 - 1 / α) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    linear_combination (-Real.log (1 / α) + Real.log (1 - 1 / α)) * hαp
  have e1 : (1 / α) ^ k = Real.exp (k * Real.log (1 / α)) := by
    rw [Real.exp_nat_mul, Real.exp_log hp]
  have e2 : (1 - 1 / α) ^ (r - k) = Real.exp (((r - k : ℕ) : ℝ) * Real.log (1 - 1 / α)) := by
    rw [Real.exp_nat_mul, Real.exp_log hq]
  unfold bb
  rw [← Real.exp_nat_mul, e1, e2, ← Real.exp_add, ← Real.exp_add, hH, Nat.cast_sub hkr]
  congr 1
  ring

lemma bb_le (α : ℝ) (hα : 1 ≤ α) : bb α ≤ 1 / α := by
  rcases eq_or_lt_of_le hα with h | h
  · subst h; simp [bb]
  · have hf := bb_pow α h 1 1 le_rfl
    rw [pow_one] at hf
    rw [hf]
    have hα0 : 0 < α := by linarith
    have hq1 : 1 - 1 / α ≤ 1 := by
      have : 0 < 1 / α := by positivity
      linarith
    have hq : 0 < 1 - 1 / α := by
      have : 1 / α < 1 := by rw [div_lt_one hα0]; exact h
      linarith
    have hl : Real.log (1 - 1 / α) ≤ 0 := Real.log_nonpos hq.le hq1
    have hE : Real.exp ((α * ((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * Real.log (1 - 1 / α)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; push_cast; nlinarith
    simp only [pow_one, Nat.sub_self, pow_zero, mul_one]
    calc 1 / α * Real.exp ((α * ((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * Real.log (1 - 1 / α))
        ≤ 1 / α * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 1 / α := mul_one _

/-- The key per-`k` estimate: with `r = ⌊αk⌋`, `choose r k * b^k ∈ [1/((m+1) e m), 1]`. -/
lemma key (m k : ℕ) (α : ℝ) (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : α * k ≤ m) :
    0 < ((⌊α * k⌋₊).choose k : ℝ) ∧ ((⌊α * k⌋₊).choose k : ℝ) * bb α ^ k ≤ 1 ∧
    1 ≤ ((m : ℝ) + 1) * (Real.exp 1 * m) * (((⌊α * k⌋₊).choose k : ℝ) * bb α ^ k) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hαk0 : 0 ≤ α * k := by positivity
  set r := ⌊α * k⌋₊ with hr
  have hr1 : (r : ℝ) ≤ α * k := Nat.floor_le hαk0
  have hr2 : α * k < r + 1 := Nat.lt_floor_add_one _
  have hkr : k ≤ r := Nat.le_floor (by nlinarith)
  have hkr' : (k : ℝ) ≤ r := by exact_mod_cast hkr
  have hrm : (r : ℝ) ≤ m := hr1.trans hk
  have hpos : 0 < (r.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkr
  refine ⟨hpos, ?_⟩
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  rcases eq_or_lt_of_le hα with h | h
  · subst h
    have hrk : r = k := by rw [hr]; simp
    have hb : bb 1 = 1 := by simp [bb]
    rw [hrk, hb]
    simp only [Nat.choose_self, Nat.cast_one, one_pow, mul_one]
    refine ⟨le_rfl, ?_⟩
    have : 1 ≤ Real.exp 1 * m := by nlinarith
    nlinarith
  · have hα0 : 0 < α := by linarith
    have hp : 0 < 1 / α := by positivity
    have hp1 : 1 / α < 1 := by rw [div_lt_one hα0]; exact h
    have hq : 0 < 1 - 1 / α := by linarith
    have hl : Real.log (1 - 1 / α) ≤ 0 := Real.log_nonpos hq.le (by linarith)
    rw [bb_pow α h k r hkr]
    set T := (r.choose k : ℝ) * (1 / α) ^ k * (1 - 1 / α) ^ (r - k) with hT
    set δ := α * k - r with hδ
    set E := Real.exp (δ * Real.log (1 - 1 / α)) with hE
    have hT0 : 0 ≤ T := by positivity
    have hδ0 : 0 ≤ δ := by linarith
    have hδ1 : δ ≤ 1 := by linarith
    have hprod : (r.choose k : ℝ) * ((1 / α) ^ k * (1 - 1 / α) ^ (r - k) * E) = T * E := by
      rw [hT]; ring
    rw [hprod]
    constructor
    · have hT1 : T ≤ 1 := by
        have := binom_term_le r k (1 / α) (1 - 1 / α) hp.le hq.le hkr
        rw [hT]; simpa using this
      have hE1 : E ≤ 1 := by rw [hE, Real.exp_le_one_iff]; nlinarith
      calc T * E ≤ 1 * 1 := mul_le_mul hT1 hE1 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    · -- mode bound
      have hmode : 1 ≤ ((r : ℝ) + 1) * T := by
        rw [hT]
        apply binom_mode r k (1 / α) hp hp1
        · rw [mul_one_div, le_div_iff₀ hα0]; nlinarith
        · rw [mul_one_div, div_le_iff₀ hα0]; nlinarith
      -- exponential correction
      have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
      have hexp : -1 - Real.log m ≤ δ * Real.log (1 - 1 / α) := by
        rcases eq_or_lt_of_le hδ0 with hd | hd
        · rw [← hd]; linarith
        · have hk1 : (1 : ℝ) ≤ k := by
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · exfalso
              have hr0 : (r : ℝ) = 0 := by rw [hr, h0]; simp
              have hk00 : (k : ℝ) = 0 := by simp [h0]
              rw [hδ, hr0, hk00] at hd; simp at hd
            · exact_mod_cast h0
          have hkα : 1 ≤ k * α := by nlinarith
          have hkα0 : 0 < k * α := by linarith
          have hδq : δ / (k * α) ≤ 1 - 1 / α := by
            rw [div_le_iff₀ hkα0]
            have : (1 - 1 / α) * (k * α) = k * α - k := by field_simp
            rw [this]; linarith
          have hlog1 : Real.log (δ / (k * α)) ≤ Real.log (1 - 1 / α) :=
            Real.log_le_log (by positivity) hδq
          rw [Real.log_div hd.ne' hkα0.ne'] at hlog1
          have hδlog : δ - 1 ≤ δ * Real.log δ := by
            have := Real.one_sub_inv_le_log_of_pos hd
            have h' : δ * (1 - δ⁻¹) = δ - 1 := by field_simp
            nlinarith
          have hlkα0 : 0 ≤ Real.log (k * α) := Real.log_nonneg hkα
          have hlkα : Real.log (k * α) ≤ Real.log m := Real.log_le_log hkα0 (by rw [mul_comm]; exact hk)
          nlinarith [mul_le_mul_of_nonneg_left hlog1 hδ0]
      have hEm : 1 ≤ (Real.exp 1 * m) * E := by
        have hm0 : (0 : ℝ) < m := by linarith
        have h1 : Real.exp 1 * m * E = Real.exp (1 + Real.log m + δ * Real.log (1 - 1 / α)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hm0, hE]
        rw [h1, Real.one_le_exp_iff]; linarith
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hrT : ((r : ℝ) + 1) * T ≤ ((m : ℝ) + 1) * T := mul_le_mul_of_nonneg_right (by linarith) hT0
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ (((m : ℝ) + 1) * T) * ((Real.exp 1 * m) * E) :=
            mul_le_mul (hmode.trans hrT) hEm zero_le_one (by positivity)
        _ = ((m : ℝ) + 1) * (Real.exp 1 * m) * (T * E) := by ring

/-- Both bounds with explicit polynomial factors. -/
lemma main_bounds (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 1 ≤ α) :
    (1 + bb α) ^ m ≤ ((m : ℝ) + 1) * Rm m α ∧
      Rm m α ≤ ((m : ℝ) + 1) * (Real.exp 1 * m) * (1 + bb α) ^ m := by
  have hα0 : 0 < α := by linarith
  have hb0 : 0 ≤ bb α := (bb_pos α).le
  set K := ⌊(m : ℝ) / α⌋₊ with hK
  have hKle : (K : ℝ) ≤ m / α := Nat.floor_le (by positivity)
  have hKlt : (m : ℝ) / α < K + 1 := Nat.lt_floor_add_one _
  have hαk : ∀ k, k ≤ K → α * k ≤ m := by
    intro k hk
    have : (k : ℝ) ≤ m / α := le_trans (by exact_mod_cast hk) hKle
    rw [le_div_iff₀ hα0] at this; linarith
  have hkm : ∀ k, k ≤ K → k ≤ m := by
    intro k hk
    have h1 := hαk k hk
    have : (k : ℝ) ≤ m := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    exact_mod_cast this
  have hterm : ∀ k, k ≤ m → (m.choose k : ℝ) * bb α ^ k ≤ (1 + bb α) ^ m := by
    intro k hk
    have := binom_term_le m k (bb α) 1 hb0 zero_le_one hk
    rw [add_comm]; simpa using this
  constructor
  · -- lower bound
    set a : ℕ → ℝ := fun k => (m.choose k : ℝ) * bb α ^ k with ha
    have hle : ∀ k, k ≤ K → a k ≤ Rm m α := by
      intro k hk
      obtain ⟨hpos, h2, -⟩ := key m k α hα hm (hαk k hk)
      unfold Rm
      refine Finset.le_sup'_of_le _ (mem_range.mpr (Nat.lt_succ_of_le hk)) ?_
      simp only [ha]
      rw [le_div_iff₀ hpos]
      calc (m.choose k : ℝ) * bb α ^ k * ((⌊α * k⌋₊).choose k : ℝ)
          = (m.choose k : ℝ) * (((⌊α * k⌋₊).choose k : ℝ) * bb α ^ k) := by ring
        _ ≤ (m.choose k : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (m.choose k : ℝ) := mul_one _
    have hdec : ∀ j, K ≤ j → j < m → a (j + 1) ≤ a j := by
      intro j hKj hj
      have hc : ((m.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq m j
      have hstep : a (j + 1) * ((j : ℝ) + 1) = a j * (((m - j : ℕ) : ℝ) * bb α) := by
        simp only [ha]; rw [pow_succ]
        linear_combination (bb α ^ j * bb α) * hc
      have hbα := bb_le α hα
      have hKj' : (K : ℝ) ≤ j := by exact_mod_cast hKj
      have hmj : ((m - j : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m j
      have hmb : (m : ℝ) * bb α ≤ m / α := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hbα (by positivity)
      have hcmp : ((m - j : ℕ) : ℝ) * bb α ≤ (j : ℝ) + 1 := by
        have := mul_le_mul_of_nonneg_right hmj hb0
        linarith
      have ha0 : 0 ≤ a j := by simp only [ha]; positivity
      refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < (j : ℝ) + 1)
      rw [hstep]; exact mul_le_mul_of_nonneg_left hcmp ha0
    have hall : ∀ k, k ≤ m → a k ≤ Rm m α := by
      intro k hk
      rcases le_total k K with h | h
      · exact hle k h
      · have : ∀ j, K ≤ j → j ≤ m → a j ≤ a K := by
          intro j hKj hjm
          induction j, hKj using Nat.le_induction with
          | base => exact le_rfl
          | succ i hKi ih => exact (hdec i hKi (by omega)).trans (ih (by omega))
        exact (this k h hk).trans (hle K le_rfl)
    have hsum : (1 + bb α) ^ m = ∑ k ∈ range (m + 1), a k := by
      rw [add_comm, add_pow]; apply sum_congr rfl; intro k _; simp only [ha]; ring
    rw [hsum]
    calc ∑ k ∈ range (m + 1), a k ≤ ∑ _k ∈ range (m + 1), Rm m α :=
          sum_le_sum (fun k hk => hall k (by have := mem_range.mp hk; omega))
      _ = ((m : ℝ) + 1) * Rm m α := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  · -- upper bound
    unfold Rm
    apply Finset.sup'_le
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨hpos, -, h3⟩ := key m k α hα hm (hαk k hkK)
    rw [div_le_iff₀ hpos]
    set Z := ((m : ℝ) + 1) * (Real.exp 1 * m)
    have hZ : 0 ≤ Z := by positivity
    calc (m.choose k : ℝ)
        ≤ (m.choose k : ℝ) * (Z * (((⌊α * k⌋₊).choose k : ℝ) * bb α ^ k)) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = Z * ((⌊α * k⌋₊).choose k : ℝ) * ((m.choose k : ℝ) * bb α ^ k) := by ring
      _ ≤ Z * ((⌊α * k⌋₊).choose k : ℝ) * (1 + bb α) ^ m :=
          mul_le_mul_of_nonneg_left (hterm k (hkm k hkK)) (by positivity)
      _ = Z * (1 + bb α) ^ m * ((⌊α * k⌋₊).choose k : ℝ) := by ring

end RandOnlineSetCoverSqrt.Dev.L64

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.Dev.L64 in
theorem chk_lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ α : ℝ, 1 ≤ α →
      (m : ℝ) ^ (-C) * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m ≤ Rm m α ∧
      Rm m α ≤ (m : ℝ) ^ C * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m := by
  refine ⟨6, by norm_num, fun m hm α hα => ?_⟩
  obtain ⟨hlo, hup⟩ := main_bounds m (by omega) α hα
  have hb : Real.exp (-(α * Real.binEntropy (1 / α))) = bb α := rfl
  rw [hb]
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h6 : (m : ℝ) ^ (6 : ℝ) = (m : ℝ) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  have hm4 : (16 : ℝ) ≤ (m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm2 4
    norm_num at this; linarith
  have hm6 : (m : ℝ) ^ (6 : ℕ) = (m : ℝ) ^ 2 * (m : ℝ) ^ 4 := by ring
  have hmsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hpoly1 : (m : ℝ) + 1 ≤ (m : ℝ) ^ (6 : ℕ) := by rw [hm6]; nlinarith
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpoly2 : ((m : ℝ) + 1) * (Real.exp 1 * m) ≤ (m : ℝ) ^ (6 : ℕ) := by
    have h1 : ((m : ℝ) + 1) * (Real.exp 1 * m) ≤ ((m : ℝ) + 1) * (3 * m) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    rw [hm6]; nlinarith
  have hX : 0 ≤ (1 + bb α) ^ m := by have := (bb_pos α).le; positivity
  have hpow6 : 0 < (m : ℝ) ^ (6 : ℕ) := by positivity
  constructor
  · rw [Real.rpow_neg hm0.le, h6, inv_mul_le_iff₀ hpow6]
    have hR : 0 ≤ Rm m α := by
      have := (hX.trans hlo); nlinarith
    nlinarith
  · rw [h6]
    exact hup.trans (mul_le_mul_of_nonneg_right hpoly2 hX)

end RandOnlineSetCoverSqrt.LowerBound.Supplement
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_lemma_6_4 := @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_lemma_6_4
