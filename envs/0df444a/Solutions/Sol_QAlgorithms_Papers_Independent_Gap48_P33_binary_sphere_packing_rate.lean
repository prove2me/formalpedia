-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.binary_sphere_packing_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:53:59.894461+00:00
-- url     : https://prove2.me/submissions/97256883-39a0-4325-8523-07e9f5a59d33

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

namespace X6P33B
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open Real Filter Topology Polynomial

theorem gen (n : ℕ) (v : Fin n → Bool) :
    (∑ x : Fin n → Bool, (X : ℕ[X]) ^ (Finset.univ.filter fun i => x i ≠ v i).card) =
      (1 + X) ^ n := by
  have h1 : ∀ x : Fin n → Bool, (X : ℕ[X]) ^ (Finset.univ.filter fun i => x i ≠ v i).card =
      ∏ i, (if x i ≠ v i then X else 1) := by
    intro x
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b ≠ v i then (X : ℕ[X]) else 1)]
  rw [Finset.prod_congr rfl (g := fun _ => 1 + X), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  intro i _
  cases h : v i <;> simp [add_comm]

theorem count (n i : ℕ) (v : Fin n → Bool) :
    (Finset.univ.filter fun x : Fin n → Bool =>
      (Finset.univ.filter fun j => x j ≠ v j).card = i).card = n.choose i := by
  have h := congrArg (fun p => Polynomial.coeff p i) (gen n v)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at h
  rw [Finset.card_filter]
  rw [Polynomial.coeff_one_add_X_pow] at h
  rw [Nat.cast_id] at h
  rw [← h]
  exact Finset.sum_congr rfl fun e _ => if_congr eq_comm rfl rfl

theorem ball_card (n t : ℕ) (v : Fin n → Bool) :
    (Finset.univ.filter fun x : Fin n → Bool =>
      (Finset.univ.filter fun j => x j ≠ v j).card ≤ t).card = ballVolume 1 n t := by
  rw [ballVolume]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin n → Bool => (Finset.univ.filter fun j => x j ≠ v j).card)
    (t := Finset.range (t + 1)) (fun e he => by simp at he ⊢; omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.filter_filter, one_pow, one_mul, ← count n i v]
  congr 1
  ext e
  simp at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

theorem packing (n k t : ℕ) (h : BinaryCode n k t) : 2 ^ k * ballVolume 1 n t ≤ 2 ^ n := by
  obtain ⟨v, hv⟩ := h
  classical
  set B : Fin (2 ^ k) → Finset (Fin n → Bool) := fun j =>
    Finset.univ.filter fun x => (Finset.univ.filter fun i => x i ≠ v j i).card ≤ t
  have hd : (Set.univ : Set (Fin (2 ^ k))).PairwiseDisjoint B := by
    intro j _ l _ hjl
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hv j l hjl x ⟨hx, hx'⟩
  have hc := Finset.card_biUnion (s := Finset.univ) (t := B) (fun j _ l _ h => hd trivial trivial h)
  have hle : (Finset.univ.biUnion B).card ≤ 2 ^ n := by
    calc _ ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ n := by simp
  rw [hc] at hle
  have : ∀ j, (B j).card = ballVolume 1 n t := fun j => ball_card n t (v j)
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  exact hle

end X6P33B

namespace X6P33B
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open Real Filter Topology

noncomputable def E (r q : ℝ) : ℝ :=
  q * log q - q * log r + (1 - q) * log (1 - q) - (1 - q) * log (1 - r)

theorem div_eq (r q : ℝ) (hr : 0 < r) (hr1 : r < 1) : binaryDivergence q r = E r q / log 2 := by
  unfold binaryDivergence E Real.logb
  have h1 : q * log (q / r) = q * log q - q * log r := by
    rcases eq_or_ne q 0 with h | h
    · simp [h]
    · rw [Real.log_div h hr.ne']; ring
  have h2 : (1 - q) * log ((1 - q) / (1 - r)) = (1 - q) * log (1 - q) - (1 - q) * log (1 - r) := by
    rcases eq_or_ne (1 - q) 0 with h | h
    · simp [h]
    · rw [Real.log_div h (by linarith)]; ring
  rw [mul_div_assoc', mul_div_assoc', ← add_div, h1, h2]; ring

theorem E_cont (r : ℝ) : Continuous (E r) := by
  unfold E
  have h1 : Continuous fun q : ℝ => q * log q := Real.continuous_mul_log
  have h2 : Continuous fun q : ℝ => (1 - q) * log (1 - q) :=
    h1.comp (continuous_const.sub continuous_id)
  fun_prop

theorem tail_eq_sum (r : ℝ) (n t : ℕ) :
    binomialLowerTail r n t = ∑ i ∈ Finset.range (t + 1), X6HamE.a n r i := by
  unfold binomialLowerTail X6HamE.a; rfl

theorem k_le' (n k V : ℕ) (hV : 1 ≤ V) (h : 2 ^ k * V ≤ 2 ^ n) :
    (k : ℝ) ≤ n - logb 2 V := by
  have hb : (0 : ℝ) < V := by exact_mod_cast hV
  have h' : (2 : ℝ) ^ k * V ≤ 2 ^ n := by exact_mod_cast h
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
  rw [Real.logb_mul (by positivity) hb.ne', Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one
    (by norm_num)] at this
  linarith

theorem bv1_pos (n t : ℕ) : 1 ≤ ballVolume 1 n t := by
  unfold ballVolume
  calc 1 = 1 ^ 0 * n.choose 0 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => 1 ^ i * n.choose i) (fun _ _ => Nat.zero_le _)
        (by simp)

theorem tail_half (n t : ℕ) :
    binomialLowerTail (1 / 2) n t = (ballVolume 1 n t : ℝ) / 2 ^ n := by
  unfold binomialLowerTail ballVolume
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases le_or_gt i n with hin | hin
  · have : (2 : ℝ) ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hin]
    rw [this]
    norm_num [div_pow]
    field_simp
  · simp [Nat.choose_eq_zero_of_lt hin]

theorem nE (r : ℝ) (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    (n : ℝ) * E r ((t : ℝ) / n) =
      (t * log ((t : ℝ) / n) + ((n : ℝ) - t) * log (1 - (t : ℝ) / n)) -
        (t * log r + ((n : ℝ) - t) * log (1 - r)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold E
  set q : ℝ := (t : ℝ) / n with hq
  have : (n : ℝ) * q = t := by rw [hq]; field_simp
  have h2 : (n : ℝ) * (1 - q) = n - t := by rw [mul_sub, this]; ring
  clear_value q
  linear_combination (log q - log r) * this + (log (1 - q) - log (1 - r)) * h2

theorem logQ (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    log (((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t)) =
      t * log ((t : ℝ) / n) + ((n : ℝ) - t) * log (1 - (t : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast ht
  have hqt : ((t : ℝ) / n) ^ t ≠ 0 := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · simp [h0]
    · apply pow_ne_zero; positivity
  have hqt' : (1 - (t : ℝ) / n) ^ (n - t) ≠ 0 := by
    rcases Nat.eq_zero_or_pos (n - t) with h0 | h0
    · simp [h0]
    · apply pow_ne_zero
      have : (t : ℝ) < n := by
        have : t < n := by omega
        exact_mod_cast this
      intro h; rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hn'.ne'] at h; linarith
  rw [Real.log_mul hqt hqt', Real.log_pow, Real.log_pow, Nat.cast_sub ht]

theorem logR (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n t : ℕ) (ht : t ≤ n) :
    log (r ^ t * (1 - r) ^ (n - t)) = t * log r + ((n : ℝ) - t) * log (1 - r) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Nat.cast_sub ht]

theorem tail_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n t : ℕ) (ht : t ≤ n) :
    X6HamE.a n r t ≤ binomialLowerTail r n t ∧ 0 < X6HamE.a n r t := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  refine ⟨?_, ?_⟩
  · rw [tail_eq_sum]
    exact Finset.single_le_sum (f := fun i => X6HamE.a n r i)
      (fun i _ => X6HamE.a_nonneg n hr.le hr1.le i) (by simp)
  · unfold X6HamE.a
    have : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
    positivity

theorem tail_lower (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    -log (n + 1) - n * E r ((t : ℝ) / n) ≤ log (binomialLowerTail r n t) := by
  obtain ⟨h1, h2⟩ := tail_pos r hr hr1 n t ht
  refine le_trans ?_ (Real.log_le_log h2 h1)
  have hl := X6HamE.lower n t hn ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Q := ((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t) with hQ
  have hQpos : 0 < Q := by
    have hq0 : 0 ≤ (t : ℝ) / n := by positivity
    have hq1 : (t : ℝ) / n ≤ 1 := by
      rw [div_le_one hn']; exact_mod_cast ht
    have h1q : 0 ≤ 1 - (t : ℝ) / n := by linarith
    have hnn : 0 ≤ Q := by rw [hQ]; positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso; unfold X6HamE.a at hl; rw [mul_assoc, ← hQ, ← h] at hl; simp at hl; linarith
  have hC : X6HamE.a n ((t : ℝ) / n) t = n.choose t * Q := by
    unfold X6HamE.a; rw [hQ]; ring
  have hR : X6HamE.a n r t = n.choose t * (r ^ t * (1 - r) ^ (n - t)) := by
    unfold X6HamE.a; ring
  have hR' : 0 < r ^ t * (1 - r) ^ (n - t) := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
  have e1 := logQ n t hn ht
  have e2 := logR r hr hr1 n t ht
  have e3 := nE r n t hn ht
  rw [← hQ] at e1
  rw [hR, Real.log_mul hc.ne' hR'.ne', e2]
  -- log C ≥ -log(n+1) - log Q
  have hlc : -log (n + 1) - log Q ≤ log (n.choose t) := by
    have h2 : 0 < (n : ℝ) + 1 := by positivity
    rw [hC] at hl
    have := Real.log_le_log (by norm_num) hl
    rw [Real.log_one, Real.log_mul h2.ne' (by positivity), Real.log_mul hc.ne' hQpos.ne'] at this
    linarith
  linarith

theorem tail_upper (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (hqr : (t : ℝ) / n ≤ r) :
    log (binomialLowerTail r n t) ≤ -(n * E r ((t : ℝ) / n)) := by
  obtain ⟨h1, h2⟩ := tail_pos r hr hr1 n t ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set q : ℝ := (t : ℝ) / n with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hn']; exact_mod_cast ht
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h1q : 0 ≤ 1 - q := by linarith
  set Q := q ^ t * (1 - q) ^ (n - t) with hQ
  set R := r ^ t * (1 - r) ^ (n - t) with hR
  have hRpos : 0 < R := by positivity
  have hQpos : 0 < Q := by
    have hl := X6HamE.lower n t hn ht
    have hnn : 0 ≤ Q := by positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso; unfold X6HamE.a at hl; rw [mul_assoc, ← hq, ← hQ, ← h] at hl; simp at hl; linarith
  have point : ∀ i ∈ Finset.range (t + 1), X6HamE.a n r i * Q ≤ X6HamE.a n q i * R := by
    intro i hi
    simp at hi
    obtain ⟨d, rfl⟩ : ∃ d, t = i + d := ⟨t - i, by omega⟩
    have hni : n - i = (n - (i + d)) + d := by omega
    have key : ((1 - r) * q) ^ d ≤ ((1 - q) * r) ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have X0 : 0 ≤ (n.choose i : ℝ) * r ^ i * q ^ i * (1 - r) ^ (n - (i + d)) * (1 - q) ^ (n - (i + d)) := by
      positivity
    have eL : X6HamE.a n r i * Q = ((n.choose i : ℝ) * r ^ i * q ^ i * (1 - r) ^ (n - (i + d)) *
        (1 - q) ^ (n - (i + d))) * ((1 - r) * q) ^ d := by
      unfold X6HamE.a; rw [hQ, hni, pow_add, pow_add, mul_pow]; ring
    have eR : X6HamE.a n q i * R = ((n.choose i : ℝ) * r ^ i * q ^ i * (1 - r) ^ (n - (i + d)) *
        (1 - q) ^ (n - (i + d))) * ((1 - q) * r) ^ d := by
      unfold X6HamE.a; rw [hR, hni, pow_add, pow_add, mul_pow]; ring
    rw [eL, eR]
    exact mul_le_mul_of_nonneg_left key X0
  have hsum : binomialLowerTail r n t * Q ≤ R := by
    rw [tail_eq_sum, Finset.sum_mul]
    refine (Finset.sum_le_sum point).trans ?_
    rw [← Finset.sum_mul]
    have : ∑ i ∈ Finset.range (t + 1), X6HamE.a n q i ≤ 1 := by
      rw [← X6HamE.sum_a n q]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by intro i; simp; omega)
        (fun i _ _ => X6HamE.a_nonneg n hq0 hq1 i)
    nlinarith
  have e1 := logQ n t hn ht
  have e2 := logR r hr hr1 n t ht
  have e3 := nE r n t hn ht
  rw [← hq, ← hQ] at e1
  rw [← hR] at e2
  rw [← hq] at e3
  have hT : 0 < binomialLowerTail r n t := lt_of_lt_of_le h2 h1
  have := Real.log_le_log (by positivity) hsum
  rw [Real.log_mul hT.ne' hQpos.ne'] at this
  linarith

end X6P33B

namespace X6P33B
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open Real Filter Topology

theorem logb_bv1 (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    n * binEntropy2 ((t : ℝ) / n) - logb 2 (n + 1) ≤ logb 2 (ballVolume 1 n t) := by
  have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
  have hge : (n.choose t : ℝ) ≤ ballVolume 1 n t := by
    have : n.choose t ≤ ballVolume 1 n t := by
      unfold ballVolume
      calc n.choose t = 1 ^ t * n.choose t := by simp
        _ ≤ _ := Finset.single_le_sum (f := fun i => 1 ^ i * n.choose i)
            (fun _ _ => Nat.zero_le _) (by rw [Finset.mem_range]; omega)
    exact_mod_cast this
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hc hge
  have h2 := X6HamE.log_choose_ge n t hn ht
  have hl2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have h3 : n * binEntropy2 ((t : ℝ) / n) - logb 2 (n + 1) ≤ logb 2 (n.choose t) := by
    unfold binEntropy2 Real.logb
    rw [mul_div_assoc', ← sub_div]
    exact div_le_div_of_nonneg_right h2 hl2.le
  linarith

theorem E_self (r : ℝ) : E r r = 0 := by unfold E; ring

theorem tail_le_one (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n t : ℕ) : binomialLowerTail r n t ≤ 1 := by
  rw [tail_eq_sum, ← X6HamE.sum_a n r]
  rcases le_or_gt t n with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg (by intro i; simp; omega)
      (fun i _ _ => X6HamE.a_nonneg n hr.le hr1.le i)
  · apply le_of_eq
    symm
    apply Finset.sum_subset (by intro i; simp; omega)
    intro i hi hi'
    simp at hi hi'
    unfold X6HamE.a; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem main (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → BinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (1 / 2) n (t n)) / (n : ℝ)) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤ 1 - binEntropy2 p ∧
    (∀ r : ℝ, 0 < r → r < 1 → p ≤ r →
      Filter.Tendsto (fun n => -Real.logb 2 (binomialLowerTail r n (t n)) / (n : ℝ))
        Filter.atTop (nhds (binaryDivergence p r))) := by
  have P1 : ∀ n, 0 < n → (k n : ℝ) ≤ n - logb 2 (ballVolume 1 n (t n)) := fun n hn =>
    k_le' n (k n) _ (bv1_pos n (t n)) (packing n (k n) (t n) (hcode n hn))
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb : (0 : ℝ) < ballVolume 1 n (t n) := by exact_mod_cast (bv1_pos n (t n))
    rw [tail_half, Real.logb_div hb.ne' (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    unfold messageRate
    apply div_le_div_of_nonneg_right _ hn'.le
    have := P1 n hn
    linarith
  · set b : ℕ → ℝ := fun n => 1 - binEntropy2 (messageRate (t n) n) +
      logb 2 ((n : ℝ) + 1) / n with hbdef
    have hcont : Continuous fun x : ℝ => 1 - binEntropy2 x := by
      unfold binEntropy2; fun_prop
    have hb : Tendsto b atTop (𝓝 (1 - binEntropy2 p)) := by
      have := ((hcont.tendsto p).comp hlimit).add X6P33O.log_tendsto
      rw [add_zero] at this
      exact this.congr fun n => rfl
    have hle : ∀ᶠ n in atTop, messageRate (k n) n ≤ b n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hk := P1 n hn
      have hl := logb_bv1 n (t n) hn (ht n hn)
      simp only [hbdef, messageRate]
      rw [div_le_iff₀ hn']
      have : (n : ℝ) * (logb 2 ((n : ℝ) + 1) / n) = logb 2 ((n : ℝ) + 1) := by field_simp
      nlinarith
    calc Filter.limsup (fun n => messageRate (k n) n) atTop ≤ Filter.limsup b atTop :=
          Filter.limsup_le_limsup hle
            (Filter.isCoboundedUnder_le_of_le atTop (x := 0)
              (fun n => by unfold messageRate; positivity)) hb.isBoundedUnder_le
      _ = _ := hb.limsup_eq
  · intro r hr hr1 hpr
    have hl2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
    rw [div_eq r p hr hr1]
    have hlim : Tendsto (fun n => (t n : ℝ) / n) atTop (𝓝 p) := hlimit
    have hlow : Tendsto (fun n => E r (min ((t n : ℝ) / n) r) / log 2) atTop (𝓝 (E r p / log 2)) := by
      have := (((E_cont r).tendsto (min p r)).comp (hlim.min tendsto_const_nhds)).div_const (log 2)
      rwa [min_eq_left hpr] at this
    have hup : Tendsto (fun n => E r ((t n : ℝ) / n) / log 2 + logb 2 ((n : ℝ) + 1) / n) atTop
        (𝓝 (E r p / log 2)) := by
      have := ((((E_cont r).tendsto p).comp hlim).div_const (log 2)).add X6P33O.log_tendsto
      rwa [add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨h1, h2⟩ := tail_pos r hr hr1 n (t n) (ht n hn)
      have hT : 0 < binomialLowerTail r n (t n) := lt_of_lt_of_le h2 h1
      rw [le_div_iff₀ hn', Real.logb,
        show ∀ x : ℝ, x / log 2 * n = (x * n) / log 2 from fun x => by ring,
        show -(log (binomialLowerTail r n (t n)) / log 2) =
          (-log (binomialLowerTail r n (t n))) / log 2 by ring]
      apply div_le_div_of_nonneg_right _ hl2.le
      rcases le_total ((t n : ℝ) / n) r with hq | hq
      · rw [min_eq_left hq]
        have := tail_upper r hr hr1 n (t n) hn (ht n hn) hq
        linarith
      · rw [min_eq_right hq, E_self]
        have := Real.log_le_log hT (tail_le_one r hr hr1 n (t n))
        rw [Real.log_one] at this
        linarith
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have := tail_lower r hr hr1 n (t n) hn (ht n hn)
      rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne', Real.logb, Real.logb,
        show ∀ x : ℝ, x / log 2 * n = (x * n) / log 2 from fun x => by ring,
        show -(log (binomialLowerTail r n (t n)) / log 2) =
          (-log (binomialLowerTail r n (t n))) / log 2 by ring, ← add_div]
      apply div_le_div_of_nonneg_right _ hl2.le
      linarith

end X6P33B

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33 in
theorem solution (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → BinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (1 / 2) n (t n)) / (n : ℝ)) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤ 1 - binEntropy2 p ∧
    (∀ r : ℝ, 0 < r → r < 1 → p ≤ r →
      Filter.Tendsto (fun n => -Real.logb 2 (binomialLowerTail r n (t n)) / (n : ℝ))
        Filter.atTop (nhds (binaryDivergence p r))) :=
  X6P33B.main k t p hp hp1 ht hcode hlimit
