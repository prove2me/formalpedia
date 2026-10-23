-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.ordinary_hamming_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:41:53.718761+00:00
-- url     : https://prove2.me/submissions/afdab6b4-ada7-4b38-b0fc-6caa42565366

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace X6Ham
open Polynomial

theorem gen (n : ℕ) :
    (∑ e : Fin n → Fin 4, (X : ℕ[X]) ^ (Finset.univ.filter fun i => e i ≠ 0).card) =
      (1 + C 3 * X) ^ n := by
  have h1 : ∀ e : Fin n → Fin 4, (X : ℕ[X]) ^ (Finset.univ.filter fun i => e i ≠ 0).card =
      ∏ i, (if e i ≠ 0 then X else 1) := by
    intro e
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 4) => if j ≠ 0 then (X : ℕ[X]) else 1)]
  simp [Fin.sum_univ_four]
  ring

theorem count (n i : ℕ) :
    (Finset.univ.filter fun e : Fin n → Fin 4 =>
      (Finset.univ.filter fun j => e j ≠ 0).card = i).card = 3 ^ i * n.choose i := by
  have h := congrArg (fun p => Polynomial.coeff p i) (gen n)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at h
  rw [Finset.card_filter]
  convert h using 1
  · exact Finset.sum_congr rfl fun e _ => if_congr eq_comm rfl rfl
  · rw [add_comm, add_pow]
    simp only [one_pow, mul_one, Polynomial.finsetSum_coeff, mul_pow, ← Polynomial.C_pow]
    have hb : ∀ b, (C (3 ^ b) * X ^ b * ((n.choose b : ℕ) : ℕ[X])).coeff i =
        if i = b then 3 ^ b * n.choose b else 0 := by
      intro b
      rw [show ((n.choose b : ℕ) : ℕ[X]) = C (n.choose b) from (Polynomial.C_eq_natCast _).symm,
        mul_comm, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, mul_comm]
    simp_rw [hb]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · simp at h
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]

end X6Ham

namespace X6HamE
open Real

/-- binomial term -/
noncomputable def a (n : ℕ) (q : ℝ) (i : ℕ) : ℝ := (n.choose i : ℝ) * q ^ i * (1 - q) ^ (n - i)

theorem a_nonneg (n : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (i : ℕ) : 0 ≤ a n q i := by
  unfold a; have : 0 ≤ 1 - q := by linarith
  positivity

theorem sum_a (n : ℕ) (q : ℝ) : ∑ i ∈ Finset.range (n + 1), a n q i = 1 := by
  have := (add_pow q (1 - q) n).symm
  simp only [add_sub_cancel, one_pow] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by unfold a; ring

/-- the ratio identity -/
theorem ratio (n : ℕ) (q : ℝ) (i : ℕ) (hi : i < n) :
    a n q (i + 1) * ((i + 1 : ℝ) * (1 - q)) = a n q i * ((n - i : ℝ) * q) := by
  unfold a
  have hc : ((n.choose (i + 1) : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ) = (n.choose i : ℝ) * ((n - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n i
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  rw [hn, pow_succ]
  push_cast at hc
  have hni : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := by rw [Nat.cast_sub hi.le]
  rw [hni] at hc
  have : (↑(n - (i + 1) + 1) : ℝ) = (n : ℝ) - i := by
    rw [← hn, Nat.cast_sub hi.le]
  linear_combination (q ^ i * (1 - q) ^ (n - (i + 1)) * q * (1 - q)) * hc

theorem max_term (n t : ℕ) (htn : t < n) (i : ℕ) (hi : i ≤ n) :
    a n ((t : ℝ) / n) i ≤ a n ((t : ℝ) / n) t := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set q : ℝ := (t : ℝ) / n with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : 1 - q = ((n : ℝ) - t) / n := by rw [hq]; field_simp
  have hnt : (0 : ℝ) < (n : ℝ) - t := by
    have : (t : ℝ) < n := by exact_mod_cast htn
    linarith
  have h1q : 0 < 1 - q := by rw [hq1]; positivity
  have hq1' : q ≤ 1 := by linarith
  -- up step
  have up : ∀ j, j < t → a n q j ≤ a n q (j + 1) := by
    intro j hj
    have r := ratio n q j (by omega)
    have hpos : (0 : ℝ) < (j + 1 : ℝ) * (1 - q) := by positivity
    have key : (j + 1 : ℝ) * (1 - q) ≤ ((n : ℝ) - j) * q := by
      rw [hq1, hq]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hn]
      have : (j : ℝ) + 1 ≤ t := by exact_mod_cast hj
      nlinarith
    have := a_nonneg n hq0 hq1' j
    by_contra hcon
    push Not at hcon
    nlinarith
  have down : ∀ j, t ≤ j → j < n → a n q (j + 1) ≤ a n q j := by
    intro j hj hjn
    have r := ratio n q j hjn
    have hpos : (0 : ℝ) < (j + 1 : ℝ) * (1 - q) := by positivity
    have key : ((n : ℝ) - j) * q ≤ (j + 1 : ℝ) * (1 - q) := by
      rw [hq1, hq]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hn]
      have : (t : ℝ) ≤ j := by exact_mod_cast hj
      have : (j : ℝ) < n := by exact_mod_cast hjn
      nlinarith
    have := a_nonneg n hq0 hq1' j
    have := a_nonneg n hq0 hq1' (j + 1)
    by_contra hcon
    push Not at hcon
    nlinarith
  rcases le_total i t with h | h
  · -- i ≤ t
    have gen : ∀ d j, j + d = t → a n q j ≤ a n q t := by
      intro d
      induction d with
      | zero => intro j hj; simp at hj; rw [hj]
      | succ d ih =>
        intro j hj
        exact (up j (by omega)).trans (ih (j + 1) (by omega))
    exact gen (t - i) i (by omega)
  · obtain ⟨d, rfl⟩ : ∃ d, i = t + d := ⟨i - t, by omega⟩
    induction d with
    | zero => simp
    | succ d ih =>
      have := down (t + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih (by omega) (by omega))

theorem lower (n t : ℕ) (hn : 0 < n) (htn : t ≤ n) :
    1 ≤ ((n : ℝ) + 1) * a n ((t : ℝ) / n) t := by
  rcases eq_or_lt_of_le htn with h | h
  · subst h
    have hn' : (t : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [a, div_self hn']
  · have hs := sum_a n ((t : ℝ) / n)
    have : ∑ i ∈ Finset.range (n + 1), a n ((t : ℝ) / n) i ≤
        ∑ _i ∈ Finset.range (n + 1), a n ((t : ℝ) / n) t :=
      Finset.sum_le_sum fun i hi => max_term n t h i (by simp at hi; omega)
    simp at this

    linarith

theorem log_choose_ge (n t : ℕ) (hn : 0 < n) (htn : t ≤ n) :
    n * binEntropy ((t : ℝ) / n) - log (n + 1) ≤ log (n.choose t) := by
  have hl := lower n t hn htn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set q : ℝ := (t : ℝ) / n with hq
  have hq0 : 0 ≤ q := by positivity
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hn']; exact htn'
  have hpos : 0 < a n q t := by
    have := a_nonneg n hq0 hq1 t
    rcases this.lt_or_eq with h | h
    · exact h
    · rw [← h] at hl; simp at hl; linarith
  have hlog : -log (n + 1) ≤ log (a n q t) := by
    have h2 : 0 < (n : ℝ) + 1 := by positivity
    have := Real.log_le_log (by norm_num) hl
    rw [Real.log_one, Real.log_mul h2.ne' hpos.ne'] at this
    linarith
  have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos htn
  have hqt : q ^ t ≠ 0 := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · simp [h0]
    · apply pow_ne_zero; rw [hq]; positivity
  have hqt' : (1 - q) ^ (n - t) ≠ 0 := by
    rcases Nat.eq_zero_or_pos (n - t) with h0 | h0
    · simp [h0]
    · apply pow_ne_zero
      have : (t : ℝ) < n := by
        have : t < n := by omega
        exact_mod_cast this
      rw [hq]; intro h; rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hn'.ne'] at h; linarith
  have ha : log (a n q t) = log (n.choose t) + t * log q + ((n : ℝ) - t) * log (1 - q) := by
    unfold a
    rw [Real.log_mul (mul_ne_zero hc.ne' hqt) hqt', Real.log_mul hc.ne' hqt, Real.log_pow,
      Real.log_pow, Nat.cast_sub htn]
  have hb : (n : ℝ) * binEntropy q = -(t * log q) - ((n : ℝ) - t) * log (1 - q) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    have : (n : ℝ) * q = t := by rw [hq]; field_simp
    clear_value q
    have h2 : (n : ℝ) * (1 - q) = n - t := by rw [mul_sub, this]; ring
    linear_combination (-(log q)) * this - (log (1 - q)) * h2
  linarith

end X6HamE

namespace X6P33O
open QAlgorithms.Papers.Independent.Gap48.P33
open Real Filter Topology QAlgorithms

theorem bv_pos (n t : ℕ) : 1 ≤ ballVolume 3 n t := by
  unfold ballVolume
  calc 1 = 3 ^ 0 * n.choose 0 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => 3 ^ i * n.choose i) (fun _ _ => Nat.zero_le _)
        (by simp)

theorem bv_ge (n t : ℕ) (ht : t ≤ n) : 3 ^ t * n.choose t ≤ ballVolume 3 n t := by
  unfold ballVolume
  exact Finset.single_le_sum (f := fun i => 3 ^ i * n.choose i) (fun _ _ => Nat.zero_le _)
    (by simp)

theorem tail_eq (n t : ℕ) (ht : t ≤ n) :
    binomialLowerTail (3 / 4) n t = (ballVolume 3 n t : ℝ) / 4 ^ n := by
  unfold binomialLowerTail ballVolume
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp at hi
  have hin : i ≤ n := by omega
  have : (4 : ℝ) ^ n = 4 ^ i * 4 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hin]
  rw [this]
  field_simp
  norm_num [div_pow]
  field_simp

/-- the per-blocklength rate inequality from the packing bound -/
theorem k_le (n k t : ℕ) (h : 2 ^ k * ballVolume 3 n t ≤ 2 ^ n) :
    (k : ℝ) ≤ n - logb 2 (ballVolume 3 n t) := by
  have hb : (0 : ℝ) < ballVolume 3 n t := by exact_mod_cast (bv_pos n t)
  have h' : (2 : ℝ) ^ k * ballVolume 3 n t ≤ 2 ^ n := by exact_mod_cast h
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
  rw [Real.logb_mul (by positivity) hb.ne', Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one
    (by norm_num)] at this
  linarith

theorem logb_bv (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    n * (binEntropy2 ((t : ℝ) / n) + (t : ℝ) / n * logb 2 3) - logb 2 (n + 1) ≤
      logb 2 (ballVolume 3 n t) := by
  have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
  have hge : ((3 : ℝ) ^ t * n.choose t) ≤ ballVolume 3 n t := by exact_mod_cast bv_ge n t ht
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hge
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow] at h1
  have h2 := X6HamE.log_choose_ge n t hn ht
  have hl2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have h3 : n * binEntropy2 ((t : ℝ) / n) - logb 2 (n + 1) ≤ logb 2 (n.choose t) := by
    unfold binEntropy2 Real.logb
    rw [mul_div_assoc', ← sub_div]
    exact div_le_div_of_nonneg_right h2 hl2.le
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (n : ℝ) * ((t : ℝ) / n * logb 2 3) = t * logb 2 3 := by field_simp
  nlinarith

noncomputable instance errFin (n t : ℕ) : Fintype (ErrorWords n t) := by
  unfold ErrorWords; infer_instance

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport) in
theorem card_err (n t : ℕ) : Fintype.card (ErrorWords n t) = ballVolume 3 n t := by
  classical
  have h1 : Fintype.card (ErrorWords n t) =
      (Finset.univ.filter fun e : Fin n → Fin 4 => pauliWeight e ≤ t).card := by
    convert Fintype.card_subtype (fun e : Fin n → Fin 4 => pauliWeight e ≤ t); rfl
  rw [h1, ballVolume]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e : Fin n → Fin 4 => pauliWeight e)
    (t := Finset.range (t + 1)) (fun e he => by simp at he ⊢; omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.filter_filter, ← X6Ham.count n i]
  congr 1
  ext e
  simp at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change _ ∧ _ ↔ pauliWeight e = i
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

theorem packing (n k t : ℕ) (hcode : OrdinaryCode n k t) :
    2 ^ k * ballVolume 3 n t ≤ 2 ^ n := by
  obtain ⟨v, hv⟩ := hcode
  have := hv.linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, card_err, finrank_euclideanSpace] at this
  simpa [Fintype.card_fun] using this

theorem log_tendsto : Tendsto (fun n : ℕ => logb 2 ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have h2 := h.div_const (log 2)
  rw [zero_div] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp, pow_one, Real.logb]
  ring_nf

theorem main (k t : ℕ → ℕ) (p : ℝ)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → OrdinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → 2 ^ k n * ballVolume 3 n (t n) ≤ 2 ^ n) ∧
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (3 / 4) n (t n)) / (n : ℝ) - 1) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤
      1 - binEntropy2 p - p * Real.logb 2 3 := by
  have P1 : ∀ n, 0 < n → 2 ^ k n * ballVolume 3 n (t n) ≤ 2 ^ n :=
    fun n hn => packing n (k n) (t n) (hcode n hn)
  refine ⟨P1, ?_, ?_⟩
  · intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb : (0 : ℝ) < ballVolume 3 n (t n) := by exact_mod_cast (bv_pos n (t n))
    have hk := k_le n (k n) (t n) (P1 n hn)
    rw [tail_eq n (t n) (ht n hn), Real.logb_div hb.ne' (by positivity), Real.logb_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    unfold messageRate
    rw [div_sub_one hn'.ne']
    apply div_le_div_of_nonneg_right _ hn'.le
    push_cast
    linarith
  · set b : ℕ → ℝ := fun n => 1 - (binEntropy2 (messageRate (t n) n) +
      messageRate (t n) n * logb 2 3) + logb 2 ((n : ℝ) + 1) / n with hbdef
    have hcont : Continuous fun x : ℝ => 1 - (binEntropy2 x + x * logb 2 3) := by
      unfold binEntropy2; fun_prop
    have hb : Tendsto b atTop (𝓝 (1 - binEntropy2 p - p * Real.logb 2 3)) := by
      have := ((hcont.tendsto p).comp hlimit).add log_tendsto
      rw [add_zero] at this
      rw [show 1 - binEntropy2 p - p * Real.logb 2 3 = 1 - (binEntropy2 p + p * logb 2 3) by ring]
      exact this.congr fun n => rfl
    have hle : ∀ᶠ n in atTop, messageRate (k n) n ≤ b n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hk := k_le n (k n) (t n) (P1 n hn)
      have hl := logb_bv n (t n) hn (ht n hn)
      simp only [hbdef, messageRate]
      rw [div_le_iff₀ hn']
      have : (n : ℝ) * (logb 2 ((n : ℝ) + 1) / n) = logb 2 ((n : ℝ) + 1) := by field_simp
      nlinarith
    calc Filter.limsup (fun n => messageRate (k n) n) atTop ≤ Filter.limsup b atTop :=
          Filter.limsup_le_limsup hle
            (Filter.isCoboundedUnder_le_of_le atTop (x := 0)
              (fun n => by unfold messageRate; positivity)) hb.isBoundedUnder_le
      _ = _ := hb.limsup_eq

end X6P33O

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33 in
theorem solution (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 3 / 4)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → OrdinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → 2 ^ k n * ballVolume 3 n (t n) ≤ 2 ^ n) ∧
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (3 / 4) n (t n)) / (n : ℝ) - 1) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤
      1 - binEntropy2 p - p * Real.logb 2 3 :=
  X6P33O.main k t p ht hcode hlimit
