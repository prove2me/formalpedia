-- Prove2me | solution 1 for Tao2022Collatz.fine_scale_mixing_of_fourier_decay
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:25:51.000451+00:00
-- url     : https://prove2.me/submissions/ed4e05e0-700f-418b-ad28-68b0d4cd3ed6

import Mathlib

set_option autoImplicit false

/-! Tao arXiv:1909.03562, Sections 6-7 layer (standalone, Mathlib only, fast to iterate).
Session 6: n-Syracuse offset as a natural number (Tao (1.29), (6.15)), its oddness,
Lemma 6.2 (injectivity of offsets, equal-sum form used by Corollary 6.3), the truncated
Syracuse distribution `mu`, the characteristic sum `chi`, and the Lean forms of
Proposition 1.14 (`Prop114`) and Proposition 1.17 (`Prop117`). -/

namespace Tao31

/-- Partial sums `ps a j = a 0 + ... + a (j-1)` (Tao's `a_{[1,j]}`). -/
def ps (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => ps a j + a j

lemma ps_succ (a : ℕ → ℕ) (j : ℕ) : ps a (j + 1) = ps a j + a j := rfl

lemma ps_mono (a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : ps a i ≤ ps a j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

lemma ps_congr (a b : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i = b i) : ps a n = ps b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ps_succ, ps_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- `2^{a_{[1,n]}} · Σ_{j<n} 3^j 2^{-a_{[1,j+1]}}` as a natural number (Tao (1.29) times `2^l`, cf. (6.15)). -/
def Fnat (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, 3 ^ j * 2 ^ (ps a n - ps a (j + 1))

lemma Fnat_zero (a : ℕ → ℕ) : Fnat a 0 = 0 := by simp [Fnat]

lemma Fnat_succ (a : ℕ → ℕ) (n : ℕ) : Fnat a (n + 1) = 2 ^ a n * Fnat a n + 3 ^ n := by
  unfold Fnat
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have hm := ps_mono a hj'
    have e : ps a (n + 1) - ps a (j + 1) = a n + (ps a n - ps a (j + 1)) := by
      rw [ps_succ]; omega
    rw [e, pow_add]; ring
  · simp

lemma Fnat_congr (a b : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i = b i) : Fnat a n = Fnat b n := by
  induction n with
  | zero => simp [Fnat_zero]
  | succ n ih => rw [Fnat_succ, Fnat_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma Fnat_odd (a : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (ha : ∀ i < n, 1 ≤ a i) : Odd (Fnat a n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fnat_succ]
  have h1 : 1 ≤ a m := ha m (by omega)
  have he : Even (2 ^ a m * Fnat a m) := by
    apply Even.mul_right
    exact (Nat.even_pow' (by omega)).2 even_two
  exact he.add_odd (Odd.pow (by decide))

lemma Fnat_pos (a : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (ha : ∀ i < n, 1 ≤ a i) : 0 < Fnat a n :=
  (Fnat_odd a n hn ha).pos

/-- `2^x u = 2^y v` with `u, v` odd forces `x = y`. -/
lemma two_pow_mul_odd_inj {x y u v : ℕ} (hu : Odd u) (hv : Odd v) (h : 2 ^ x * u = 2 ^ y * v) :
    x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exfalso
    have e : 2 ^ x * u = 2 ^ x * (2 ^ (y - x) * v) := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hxy.le]
    have := Nat.eq_of_mul_eq_mul_left (by positivity) e
    have hev : Even (2 ^ (y - x) * v) :=
      Even.mul_right ((Nat.even_pow' (by omega)).2 even_two) _
    rw [← this] at hev
    exact (Nat.not_even_iff_odd.2 hu) hev
  · exact hxy
  · exfalso
    have e : 2 ^ y * v = 2 ^ y * (2 ^ (x - y) * u) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hxy.le]
    have := Nat.eq_of_mul_eq_mul_left (by positivity) e
    have hev : Even (2 ^ (x - y) * u) :=
      Even.mul_right ((Nat.even_pow' (by omega)).2 even_two) _
    rw [← this] at hev
    exact (Nat.not_even_iff_odd.2 hv) hev

/-- Tao Lemma 6.2 (injectivity of offsets), in the equal-total form used for (6.15). -/
theorem Fnat_inj (a b : ℕ → ℕ) (n : ℕ) (ha : ∀ i < n, 1 ≤ a i) (hb : ∀ i < n, 1 ≤ b i)
    (hs : ps a n = ps b n) (hF : Fnat a n = Fnat b n) : ∀ i < n, a i = b i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [Fnat_succ, Fnat_succ] at hF
    have hF' : 2 ^ a n * Fnat a n = 2 ^ b n * Fnat b n := by omega
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa [ps] using hs
    · have hoa := Fnat_odd a n hpos (fun i hi => ha i (by omega))
      have hob := Fnat_odd b n hpos (fun i hi => hb i (by omega))
      have hab : a n = b n := two_pow_mul_odd_inj hoa hob hF'
      rw [hab] at hF'
      have hFF : Fnat a n = Fnat b n := Nat.eq_of_mul_eq_mul_left (by positivity) hF'
      have hs' : ps a n = ps b n := by rw [ps_succ, ps_succ, hab] at hs; omega
      have ih' := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)) hs' hFF
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact ih' i h
      · rw [h]; exact hab

/-- Pad a tuple with `1`s (same definition as in the main draft). -/
def padv {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then w ⟨i, h⟩ else 1

/-- The Syracuse offset mod `3^n`: `Σ_{j<n} 3^j 2^{-a_{[1,j+1]}} = Fnat · 2^{-a_{[1,n]}}` (Tao (1.29)). -/
noncomputable def syrZ (n : ℕ) (a : ℕ → ℕ) : ZMod (3 ^ n) :=
  (Fnat a n : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a n

/-- Tuples `a ∈ [1,K]^n` (Geom(2)^n truncated at `K`; weight `2^{-|a|}`). -/
noncomputable def Box (n K : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 K)

open Classical in
/-- Truncated distribution of `Syrac(Z/3^n)`: `mu n K Y = Σ_{a ∈ [1,K]^n, syr a = Y} 2^{-|a|}`. -/
noncomputable def mu (n K : ℕ) (Y : ZMod (3 ^ n)) : ℝ :=
  ∑ w ∈ (Box n K).filter (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)

/-- Truncated characteristic sum `E e^{-2πi ξ Syrac(Z/3^n)/3^n}` (Tao (1.28)). -/
noncomputable def chi (n K : ℕ) (ξ : ℤ) : ℂ :=
  ∑ w ∈ Box n K, ((1 : ℂ) / 2) ^ (∑ i, w i) *
    Complex.exp (-(2 * Real.pi * Complex.I) * ξ * ((syrZ n (padv w)).val : ℂ) / 3 ^ n)

open Classical in
/-- Tao's oscillation (1.27) at 3-adic scale `3^{-m}`. -/
noncomputable def Osc (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ m / 3 ^ n *
    ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'|

/-- Tao Proposition 1.14 (fine-scale mixing), for truncations `K ≥ n`. -/
def Prop114 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    Osc m n (mu n K) ≤ C * (m : ℝ) ^ (-A)

/-- Tao Proposition 1.17 (decay of the characteristic function), for truncations `K ≥ n`. -/
def Prop117 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖chi n K ξ‖ ≤ C * (n : ℝ) ^ (-A)

/-- `2 · 2⁻¹ = 1` in `ZMod (3^n)`. -/
lemma two_mul_inv (n : ℕ) : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
  have hc : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 hc
  simpa using this

/-- `2^{a_{[1,n]}} · syr a = Fnat a n` in `ZMod (3^n)`. -/
lemma two_pow_syrZ (n : ℕ) (a : ℕ → ℕ) :
    (2 : ZMod (3 ^ n)) ^ ps a n * syrZ n a = (Fnat a n : ZMod (3 ^ n)) := by
  unfold syrZ
  rw [mul_left_comm, ← mul_pow, two_mul_inv, one_pow, mul_one]

/-! Tao Lemma 2.2 (Chernoff bound for sums of Geom(2)), in the truncated box model. -/

lemma box_gen (n K : ℕ) (z : ℝ) :
    ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i) =
      (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := by
  calc ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)
      = ∑ w ∈ Box n K, ∏ i, (z / 2) ^ (w i) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.prod_pow_eq_pow_sum, div_eq_mul_one_div z 2, mul_pow, mul_comm]
    _ = ∏ _i : Fin n, ∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a := (Finset.prod_univ_sum _ _).symm
    _ = (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := Fin.prod_const n _

lemma geom_Icc_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ x / (1 - x) := by
  calc ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ ∑ a ∈ Finset.Ico 1 (K + 1), x ^ a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢
          omega
        · intro a _ _; positivity
    _ ≤ x ^ 1 / (1 - x) := geom_sum_Ico_le_of_lt_one h0 h1
    _ = x / (1 - x) := by rw [pow_one]

lemma tail_gen (n K : ℕ) (P : (Fin n → ℕ) → Prop) [DecidablePred P] (z s : ℝ) (hz : 0 < z)
    (hz2 : z < 2) (hP : ∀ w ∈ Box n K, P w → 1 ≤ z ^ (-s + ((∑ i, w i : ℕ) : ℝ))) :
    ∑ w ∈ (Box n K).filter P, ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      z ^ (-s) * ((z / 2) / (1 - z / 2)) ^ n := by
  have hx0 : 0 ≤ z / 2 := by positivity
  have hx1 : z / 2 < 1 := by linarith
  calc ∑ w ∈ (Box n K).filter P, ((1 : ℝ) / 2) ^ (∑ i, w i)
      ≤ ∑ w ∈ (Box n K).filter P, z ^ (-s) * (((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have h1 := hP w hw'.1 hw'.2
        rw [Real.rpow_add hz, Real.rpow_natCast] at h1
        have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, w i) := by positivity
        (first | linarith | nlinarith)
    _ ≤ ∑ w ∈ Box n K, z ^ (-s) * (((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro w _ _; positivity
    _ = z ^ (-s) * (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := by rw [← Finset.mul_sum, box_gen]
    _ ≤ z ^ (-s) * ((z / 2) / (1 - z / 2)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => by positivity))
          (geom_Icc_le _ hx0 hx1 K) n

lemma log_one_add_ge (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1 / 6) :
    d - 3 / 2 * d ^ 2 ≤ Real.log (1 + d) := by
  have hab : |(-d)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
    abs_neg, abs_of_nonneg h0] at h
  have hq : d ^ 2 / (1 - d) ≤ 3 / 2 * d ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; (first | linarith | nlinarith)
  have := (abs_le.1 h).1
  rw [add_comm] at this
  linarith

lemma neg_log_one_sub_le (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1 / 6) :
    -Real.log (1 - d) ≤ d + 3 / 2 * d ^ 2 ∧ d ≤ -Real.log (1 - d) := by
  have hab : |d| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one,
    abs_of_nonneg h0] at h
  have hq : d ^ 2 / (1 - d) ≤ 3 / 2 * d ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; (first | linarith | nlinarith)
  have hl : Real.log (1 - d) ≤ (1 - d) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  constructor
  · have := (abs_le.1 h).1; linarith
  · linarith

open Classical in
/-- Tao Lemma 2.2, upper tail: `P(|a| ≥ 2n + t) ≤ exp(-t min(t/n,1)/24)`. -/
theorem chernoff_up (n K : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ∑ w ∈ (Box n K).filter (fun w => 2 * (n : ℝ) + t ≤ ((∑ i, w i : ℕ) : ℝ)),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(t * min (t / n) 1) / 24) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set μ := min (t / n) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (div_nonneg ht (by linarith)) zero_le_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμt : (n : ℝ) * μ ≤ t := by
    have : μ ≤ t / n := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set d := μ / 6 with hd
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 / 6 := by rw [hd]; linarith
  have hz : 0 < 1 + d := by linarith
  have hb := tail_gen n K (fun w => 2 * (n : ℝ) + t ≤ ((∑ i, w i : ℕ) : ℝ)) (1 + d)
    (2 * n + t) hz (by linarith) (by
      intro w _ hw
      apply Real.one_le_rpow (by linarith) (by linarith))
  refine hb.trans ?_
  have eqE : (1 + d) ^ (-(2 * (n : ℝ) + t)) * ((1 + d) / 2 / (1 - (1 + d) / 2)) ^ n =
      Real.exp ((-(2 * n + t)) * Real.log (1 + d) + n * (Real.log (1 + d) - Real.log (1 - d))) := by
    have e1 : (1 + d) / 2 / (1 - (1 + d) / 2) = (1 + d) / (1 - d) := by
      have h1 : (1 : ℝ) + d ≠ 0 := by linarith
      have h2 : (1 : ℝ) - d ≠ 0 := by linarith
      rw [div_div, div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e1, Real.rpow_def_of_pos hz, ← Real.exp_log (show 0 < ((1 + d) / (1 - d)) ^ n by
      apply pow_pos; apply div_pos <;> linarith), ← Real.exp_add, Real.log_pow,
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  rw [eqE]
  · apply Real.exp_le_exp.2
    have l1 := log_one_add_ge d hd0 hd1
    have l2 := (neg_log_one_sub_le d hd0 hd1).1
    have s1 : (n + t) * (d - 3 / 2 * d ^ 2) ≤ (n + t) * Real.log (1 + d) :=
      mul_le_mul_of_nonneg_left l1 (by linarith)
    have s2 : (n : ℝ) * -Real.log (1 - d) ≤ n * (d + 3 / 2 * d ^ 2) :=
      mul_le_mul_of_nonneg_left l2 (by linarith)
    have s3 : (n : ℝ) * μ * μ ≤ t * μ := mul_le_mul_of_nonneg_right hμt hμ0
    have s4 : t * μ * μ ≤ t * μ := by (first | linarith [mul_nonneg ht hμ0] | nlinarith [mul_nonneg ht hμ0])
    rw [hd] at s1 s2 ⊢
    (first | linarith [s1, s2, s3, s4] | nlinarith [s1, s2, s3, s4])

open Classical in
/-- Tao Lemma 2.2, lower tail: `P(|a| ≤ 2n - t) ≤ exp(-t min(t/n,1)/24)`. -/
theorem chernoff_down (n K : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ∑ w ∈ (Box n K).filter (fun w => ((∑ i, w i : ℕ) : ℝ) ≤ 2 * (n : ℝ) - t),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(t * min (t / n) 1) / 24) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set μ := min (t / n) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (div_nonneg ht (by linarith)) zero_le_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμt : (n : ℝ) * μ ≤ t := by
    have : μ ≤ t / n := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set d := μ / 6 with hd
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 / 6 := by rw [hd]; linarith
  have hz : 0 < 1 - d := by linarith
  have hb := tail_gen n K (fun w => ((∑ i, w i : ℕ) : ℝ) ≤ 2 * (n : ℝ) - t) (1 - d)
    (2 * n - t) hz (by linarith) (by
      intro w _ hw
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz (by linarith)
        (by linarith))
  refine hb.trans ?_
  have eqE : (1 - d) ^ (-(2 * (n : ℝ) - t)) * ((1 - d) / 2 / (1 - (1 - d) / 2)) ^ n =
      Real.exp ((-(2 * n - t)) * Real.log (1 - d) + n * (Real.log (1 - d) - Real.log (1 + d))) := by
    have e1 : (1 - d) / 2 / (1 - (1 - d) / 2) = (1 - d) / (1 + d) := by
      have h1 : (1 : ℝ) + d ≠ 0 := by linarith
      have h2 : (1 : ℝ) - d ≠ 0 := by linarith
      rw [div_div, div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e1, Real.rpow_def_of_pos hz, ← Real.exp_log (show 0 < ((1 - d) / (1 + d)) ^ n by
      apply pow_pos; apply div_pos <;> linarith), ← Real.exp_add, Real.log_pow,
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  rw [eqE]
  · apply Real.exp_le_exp.2
    have l1 := log_one_add_ge d hd0 hd1
    obtain ⟨l2, l3⟩ := neg_log_one_sub_le d hd0 hd1
    have hnd : (n : ℝ) * d ≤ t / 6 := by rw [hd]; linarith
    set e := -Real.log (1 - d) - d with he
    have he0 : 0 ≤ e := by linarith
    have he1 : e ≤ 3 / 2 * d ^ 2 := by linarith
    have key : (-(2 * n - t)) * Real.log (1 - d) + n * (Real.log (1 - d) - Real.log (1 + d))
        = (n - t) * d + n * e - t * e - n * Real.log (1 + d) := by rw [he]; ring
    rw [key]
    have s1 : (n : ℝ) * (d - 3 / 2 * d ^ 2) ≤ n * Real.log (1 + d) :=
      mul_le_mul_of_nonneg_left l1 (by linarith)
    have s2 : (n : ℝ) * e ≤ n * (3 / 2 * d ^ 2) := mul_le_mul_of_nonneg_left he1 (by linarith)
    have s3 : (n : ℝ) * μ * μ ≤ t * μ := mul_le_mul_of_nonneg_right hμt hμ0
    have s5 : 0 ≤ t * e := mul_nonneg ht he0
    have s6 : 0 ≤ t * μ := mul_nonneg ht hμ0
    rw [hd] at s1 s2 ⊢
    (first | linarith [s1, s2, s3, s5, s6] | nlinarith [s1, s2, s3, s5, s6])

/-! Block splitting of the offset (Tao (1.5), (1.23); used in Section 6 on the event `C_{k,l}`). -/

lemma ps_add (a : ℕ → ℕ) (p q : ℕ) : ps a (p + q) = ps a p + ps (fun i => a (p + i)) q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [← add_assoc, ps_succ, ih, ps_succ, add_assoc]

lemma Fnat_add (a : ℕ → ℕ) (p q : ℕ) :
    Fnat a (p + q) = 2 ^ ps (fun i => a (p + i)) q * Fnat a p + 3 ^ p * Fnat (fun i => a (p + i)) q := by
  induction q with
  | zero => simp [Fnat_zero, ps]
  | succ q ih =>
    rw [← add_assoc, Fnat_succ, ih, ps_succ, Fnat_succ]
    simp only [pow_add]
    ring

/-- Splitting `syr` at `p`: `syr_{p+q}(a) = syr_p(a) + 3^p 2^{-a_{[1,p]}} syr_q(a_{p+1..})` in `ZMod (3^{p+q})`. -/
lemma syrZ_split (a : ℕ → ℕ) (p q : ℕ) :
    syrZ (p + q) a = (Fnat a p : ZMod (3 ^ (p + q))) * ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p +
      3 ^ p * ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p *
        ((Fnat (fun i => a (p + i)) q : ZMod (3 ^ (p + q))) *
          ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps (fun i => a (p + i)) q) := by
  unfold syrZ
  rw [Fnat_add, ps_add, pow_add ((2 : ZMod (3 ^ (p + q)))⁻¹)]
  have h2 : (2 : ZMod (3 ^ (p + q))) ^ ps (fun i => a (p + i)) q *
      ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps (fun i => a (p + i)) q = 1 := by
    rw [← mul_pow, two_mul_inv, one_pow]
  push_cast
  linear_combination ((Fnat a p : ZMod (3 ^ (p + q))) *
    ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p) * h2

/-- The character in `chi` is the standard additive character of `ZMod (3^n)`. -/
lemma exp_eq_stdAddChar (n : ℕ) (ξ : ℤ) (Y : ZMod (3 ^ n)) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ξ * (Y.val : ℂ) / 3 ^ n) =
      ZMod.stdAddChar (-(ξ : ZMod (3 ^ n)) * Y) := by
  have h := ZMod.stdAddChar_coe (N := 3 ^ n) (-(ξ * (Y.val : ℤ)))
  have hc : (((-(ξ * (Y.val : ℤ))) : ℤ) : ZMod (3 ^ n)) = -(ξ : ZMod (3 ^ n)) * Y := by
    push_cast; rw [ZMod.natCast_zmod_val]; ring
  rw [hc] at h
  rw [h]
  congr 1
  push_cast
  ring

lemma chi_eq (n K : ℕ) (ξ : ℤ) :
    chi n K ξ = ∑ w ∈ Box n K, ((1 : ℂ) / 2) ^ (∑ i, w i) *
      ZMod.stdAddChar (-(ξ : ZMod (3 ^ n)) * syrZ n (padv w)) := by
  unfold chi
  apply Finset.sum_congr rfl
  intro w _
  rw [exp_eq_stdAddChar]


/-! Item 7d (S7): Plancherel on `ZMod (3^n)` and the Fourier form of `Osc`. -/

section Four
open Finset


local instance neZeroPow3 (n : ℕ) : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩

/-- Fourier coefficient on `ZMod N` with the standard character. -/
noncomputable def fc {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (ξ : ZMod N) : ℂ :=
  ∑ Y, g Y * ZMod.stdAddChar (-(ξ * Y))

lemma sum_stdAddChar (N : ℕ) [NeZero N] (b : ZMod N) :
    ∑ x : ZMod N, ZMod.stdAddChar (x * b) = if b = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

lemma ofReal_normsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Plancherel/Parseval on `ZMod N`. -/
theorem parseval (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    ∑ ξ, ‖fc g ξ‖ ^ 2 = (N : ℝ) * ∑ Y, ‖g Y‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
  simp_rw [ofReal_normsq]
  have h1 : ∀ ξ, fc g ξ * (starRingEnd ℂ) (fc g ξ) =
      ∑ Y, ∑ Y', g Y * (starRingEnd ℂ) (g Y') * ZMod.stdAddChar (ξ * (Y' - Y)) := by
    intro ξ
    unfold fc
    rw [map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun Y' _ => ?_))
    rw [map_mul, ← AddChar.map_neg_eq_conj, neg_neg, mul_sub, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    ring
  simp_rw [h1]
  calc ∑ ξ, ∑ Y, ∑ Y', g Y * (starRingEnd ℂ) (g Y') * ZMod.stdAddChar (ξ * (Y' - Y))
      = ∑ Y, ∑ Y', ∑ ξ, g Y * (starRingEnd ℂ) (g Y') * ZMod.stdAddChar (ξ * (Y' - Y)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun Y _ => Finset.sum_comm)
    _ = ∑ Y, ∑ Y', g Y * (starRingEnd ℂ) (g Y') * (if Y' - Y = 0 then (N : ℂ) else 0) := by
        simp_rw [← Finset.mul_sum, sum_stdAddChar]
    _ = ∑ Y, (N : ℂ) * (g Y * (starRingEnd ℂ) (g Y)) := by
        refine Finset.sum_congr rfl (fun Y _ => ?_)
        simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
    _ = (N : ℂ) * ∑ Y, g Y * (starRingEnd ℂ) (g Y) := by rw [Finset.mul_sum]

/-- `3^{n-m} Z` depends only on `Z mod 3^m`. -/
lemma three_pow_mul_eq (n m : ℕ) (hmn : m ≤ n) (Z : ZMod (3 ^ n)) :
    (3 : ZMod (3 ^ n)) ^ (n - m) * Z = 3 ^ (n - m) * ((Z.val % 3 ^ m : ℕ) : ZMod (3 ^ n)) := by
  have h3 : (3 : ZMod (3 ^ n)) ^ (n - m) * 3 ^ m = 0 := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
    exact_mod_cast ZMod.natCast_self (3 ^ n)
  have hZ : Z = (((3 ^ m * (Z.val / 3 ^ m) + Z.val % 3 ^ m : ℕ)) : ZMod (3 ^ n)) := by
    rw [Nat.div_add_mod, ZMod.natCast_zmod_val]
  conv_lhs => rw [hZ]
  push_cast
  linear_combination ((Z.val / 3 ^ m : ℕ) : ZMod (3 ^ n)) * h3

lemma mul_eq_of_fib (n m : ℕ) (hmn : m ≤ n) (ξ : ZMod (3 ^ n)) (hξ : 3 ^ (n - m) ∣ ξ.val)
    (Y Y' : ZMod (3 ^ n)) (h : Y.val % 3 ^ m = Y'.val % 3 ^ m) : ξ * Y = ξ * Y' := by
  obtain ⟨q, hq⟩ := hξ
  have hξ' : ξ = (3 : ZMod (3 ^ n)) ^ (n - m) * (q : ZMod (3 ^ n)) := by
    have e : ((ξ.val : ℕ) : ZMod (3 ^ n)) = ((3 ^ (n - m) * q : ℕ) : ZMod (3 ^ n)) := by rw [hq]
    rw [ZMod.natCast_zmod_val] at e
    rw [e]; push_cast; ring
  calc ξ * Y = (q : ZMod (3 ^ n)) * (3 ^ (n - m) * Y) := by rw [hξ']; ring
    _ = (q : ZMod (3 ^ n)) * (3 ^ (n - m) * Y') := by
        rw [three_pow_mul_eq n m hmn Y, three_pow_mul_eq n m hmn Y', h]
    _ = ξ * Y' := by rw [hξ']; ring

lemma mul_three_pow_ne (n m : ℕ) (hmn : m ≤ n) (ξ : ZMod (3 ^ n)) (hξ : ¬ 3 ^ (n - m) ∣ ξ.val) :
    ξ * (3 : ZMod (3 ^ n)) ^ m ≠ 0 := by
  intro h0
  apply hξ
  have h1 : (((ξ.val * 3 ^ m : ℕ)) : ZMod (3 ^ n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_pow, Nat.cast_ofNat]; exact h0
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : 3 ^ (n - m) * 3 ^ m ∣ ξ.val * 3 ^ m := by rwa [← pow_add, Nat.sub_add_cancel hmn]
  exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h2

lemma val_add_three_pow (n m : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    (Y + (3 : ZMod (3 ^ n)) ^ m).val % 3 ^ m = Y.val % 3 ^ m := by
  have hd : 3 ^ m ∣ 3 ^ n := pow_dvd_pow 3 hmn
  have e : (3 : ZMod (3 ^ n)) ^ m = ((3 ^ m : ℕ) : ZMod (3 ^ n)) := by simp
  rw [e, ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hd, Nat.add_mod,
    Nat.mod_mod_of_dvd _ hd, Nat.mod_self, add_zero, Nat.mod_mod]

/-- Each 3-adic fibre of `ZMod (3^n)` at scale `3^m` has `3^{n-m}` points. -/
lemma fib_card (n m : ℕ) (hmn : m ≤ n) (Y' : ZMod (3 ^ n)) :
    (univ.filter (fun Y : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m)).card = 3 ^ (n - m) := by
  have h0 : univ.filter (fun Y : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m) =
      univ.filter (fun Y : ZMod (3 ^ n) => Y.val % 3 ^ m = Y'.val % 3 ^ m) :=
    Finset.filter_congr (fun _ _ => eq_comm)
  have h1 : (univ.filter (fun Y : ZMod (3 ^ n) => Y.val % 3 ^ m = Y'.val % 3 ^ m)).card =
      ((range (3 ^ n)).filter (fun x => x % 3 ^ m = Y'.val % 3 ^ m)).card := by
    apply Finset.card_nbij' (fun Y : ZMod (3 ^ n) => Y.val) (fun x : ℕ => (x : ZMod (3 ^ n)))
    · intro Y hY
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hY ⊢
      exact ⟨ZMod.val_lt Y, hY⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hx ⊢
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx.1]; exact hx.2
    · intro Y _; exact ZMod.natCast_zmod_val Y
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
      show ((x : ZMod (3 ^ n))).val = x
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx.1]
  rw [h0, h1, ← Nat.count_eq_card_filter_range]
  have hr : 0 < 3 ^ m := by positivity
  have hc := Nat.count_modEq_card (3 ^ n) hr Y'.val
  have hm0 : 3 ^ n % 3 ^ m = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow 3 hmn)
  rw [hm0, Nat.pow_div hmn (by norm_num)] at hc
  simp only [Nat.not_lt_zero, if_false, add_zero] at hc
  exact hc

/-- Character sum over a 3-adic fibre: `3^{n-m} ψ(-ξY')` if `3^{n-m} ∣ ξ`, else `0`. -/
lemma fib_sum (n m : ℕ) (hmn : m ≤ n) (ξ Y' : ZMod (3 ^ n)) :
    ∑ Y ∈ univ.filter (fun Y : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m),
      ZMod.stdAddChar (-(ξ * Y)) =
    if 3 ^ (n - m) ∣ ξ.val then (3 : ℂ) ^ (n - m) * ZMod.stdAddChar (-(ξ * Y')) else 0 := by
  split_ifs with hξ
  · have hc : ∀ Y ∈ univ.filter (fun Y : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m),
        ZMod.stdAddChar (-(ξ * Y)) = ZMod.stdAddChar (-(ξ * Y')) := fun Y hY => by
      rw [mul_eq_of_fib n m hmn ξ hξ Y Y' (Finset.mem_filter.1 hY).2.symm]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, fib_card n m hmn, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  · rw [Finset.sum_filter]
    set f : ZMod (3 ^ n) → ℂ := fun Y =>
      if Y'.val % 3 ^ m = Y.val % 3 ^ m then ZMod.stdAddChar (-(ξ * Y)) else 0 with hf
    have hshift : ∀ Y, f (Y + (3 : ZMod (3 ^ n)) ^ m) =
        ZMod.stdAddChar (-(ξ * (3 : ZMod (3 ^ n)) ^ m)) * f Y := by
      intro Y
      simp only [hf, val_add_three_pow n m hmn Y]
      split_ifs
      · rw [← AddChar.map_add_eq_mul]; congr 1; ring
      · simp
    have hS : ∑ Y, f Y = ZMod.stdAddChar (-(ξ * (3 : ZMod (3 ^ n)) ^ m)) * ∑ Y, f Y := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight ((3 : ZMod (3 ^ n)) ^ m)) f]
      exact Finset.sum_congr rfl (fun Y _ => hshift Y)
    have hne : ZMod.stdAddChar (-(ξ * (3 : ZMod (3 ^ n)) ^ m)) ≠ (1 : ℂ) := by
      intro h1
      have h0 : ZMod.stdAddChar (N := 3 ^ n) (-(ξ * (3 : ZMod (3 ^ n)) ^ m)) =
          ZMod.stdAddChar (N := 3 ^ n) 0 := by rw [h1, AddChar.map_zero_eq_one]
      exact mul_three_pow_ne n m hmn ξ hξ (neg_eq_zero.1 (ZMod.injective_stdAddChar h0))
    have h2 : (1 - ZMod.stdAddChar (-(ξ * (3 : ZMod (3 ^ n)) ^ m))) * ∑ Y, f Y = 0 := by
      rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

/-- Fibre average at scale `3^m` (the subtracted term in `Osc`). -/
noncomputable def favg (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) : ℝ :=
  (3 : ℝ) ^ m / 3 ^ n *
    ∑ Y' ∈ univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'

/-- Fibre averaging = Fourier projection onto frequencies divisible by `3^{n-m}`. -/
lemma fc_favg (n m : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (ξ : ZMod (3 ^ n)) :
    fc (fun Y => ((favg m n c Y : ℝ) : ℂ)) ξ =
      if 3 ^ (n - m) ∣ ξ.val then fc (fun Y => ((c Y : ℝ) : ℂ)) ξ else 0 := by
  have hk : ((3 : ℂ) ^ m / 3 ^ n) * 3 ^ (n - m) = 1 := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_cancel' hmn,
      div_self (pow_ne_zero _ (by norm_num))]
  have e1 : fc (fun Y => ((favg m n c Y : ℝ) : ℂ)) ξ =
      ∑ Y' : ZMod (3 ^ n), ∑ Y : ZMod (3 ^ n), (if Y'.val % 3 ^ m = Y.val % 3 ^ m then
        ((3 : ℂ) ^ m / 3 ^ n) * (c Y' : ℂ) * ZMod.stdAddChar (-(ξ * Y)) else 0) := by
    rw [Finset.sum_comm]
    unfold fc favg
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    push_cast
    rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Y' _ => ?_)
    split_ifs <;> ring
  have e2 : ∀ Y' : ZMod (3 ^ n), ∑ Y : ZMod (3 ^ n), (if Y'.val % 3 ^ m = Y.val % 3 ^ m then
        ((3 : ℂ) ^ m / 3 ^ n) * (c Y' : ℂ) * ZMod.stdAddChar (-(ξ * Y)) else 0) =
      ((3 : ℂ) ^ m / 3 ^ n) * (c Y' : ℂ) *
        ∑ Y ∈ univ.filter (fun Y : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m),
          ZMod.stdAddChar (-(ξ * Y)) := by
    intro Y'
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [e1]
  simp_rw [e2, fib_sum n m hmn]
  unfold fc
  by_cases hξ : 3 ^ (n - m) ∣ ξ.val
  · simp only [hξ, if_true]
    refine Finset.sum_congr rfl (fun Y' _ => ?_)
    linear_combination ((c Y' : ℂ) * ZMod.stdAddChar (-(ξ * Y'))) * hk
  · simp only [hξ, if_false, mul_zero, Finset.sum_const_zero]

/-- Item 7d: the oscillation is controlled by the `L²` mass of the Fourier coefficients at
frequencies not divisible by `3^{n-m}` (Plancherel + Cauchy-Schwarz). -/
theorem osc_le_fourier (n m : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    Osc m n c ≤ Real.sqrt (∑ ξ ∈ univ.filter (fun ξ : ZMod (3 ^ n) => ¬ 3 ^ (n - m) ∣ ξ.val),
      ‖fc (fun Y => ((c Y : ℝ) : ℂ)) ξ‖ ^ 2) := by
  set d : ZMod (3 ^ n) → ℝ := fun Y => c Y - favg m n c Y with hd
  have hosc : Osc m n c = ∑ Y, |d Y| := rfl
  have hfd : ∀ ξ, fc (fun Y => ((d Y : ℝ) : ℂ)) ξ =
      if 3 ^ (n - m) ∣ ξ.val then 0 else fc (fun Y => ((c Y : ℝ) : ℂ)) ξ := by
    intro ξ
    have h : fc (fun Y => ((d Y : ℝ) : ℂ)) ξ = fc (fun Y => ((c Y : ℝ) : ℂ)) ξ -
        fc (fun Y => ((favg m n c Y : ℝ) : ℂ)) ξ := by
      unfold fc
      simp only [hd, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    rw [h, fc_favg n m hmn]
    split_ifs <;> simp
  have hpar := parseval (3 ^ n) (fun Y => ((d Y : ℝ) : ℂ))
  simp_rw [hfd] at hpar
  have hL : ∑ ξ : ZMod (3 ^ n), ‖(if 3 ^ (n - m) ∣ ξ.val then (0 : ℂ)
        else fc (fun Y => ((c Y : ℝ) : ℂ)) ξ)‖ ^ 2 =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod (3 ^ n) => ¬ 3 ^ (n - m) ∣ ξ.val),
        ‖fc (fun Y => ((c Y : ℝ) : ℂ)) ξ‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    split_ifs <;> simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod (3 ^ n)))
    (fun _ => (1 : ℝ)) (fun Y => |d Y|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpar
  rw [hosc]
  have hnn : 0 ≤ ∑ Y, |d Y| := Finset.sum_nonneg (fun Y _ => abs_nonneg _)
  rw [← abs_of_nonneg hnn]
  apply Real.abs_le_sqrt
  rw [← hL, hpar]
  exact hcs

/-- `Osc` is subadditive. -/
lemma Osc_add (m n : ℕ) (c₁ c₂ : ZMod (3 ^ n) → ℝ) :
    Osc m n (fun Y => c₁ Y + c₂ Y) ≤ Osc m n c₁ + Osc m n c₂ := by
  unfold Osc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  rw [Finset.sum_add_distrib]
  calc _ = |(c₁ Y - (3 : ℝ) ^ m / 3 ^ n *
          ∑ Y' ∈ univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c₁ Y') +
        (c₂ Y - (3 : ℝ) ^ m / 3 ^ n *
          ∑ Y' ∈ univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c₂ Y')| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _

/-- Trivial bound `Osc ≤ 2 ‖c‖₁` (for exceptional events). -/
lemma Osc_le_l1 (n m : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    Osc m n c ≤ 2 * ∑ Y, |c Y| := by
  have hk : (3 : ℝ) ^ m / 3 ^ n * 3 ^ (n - m) = 1 := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_cancel' hmn, div_self (by positivity)]
  have hswap : ∑ Y : ZMod (3 ^ n),
      ∑ Y' ∈ univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), |c Y'| =
      ∑ Y' : ZMod (3 ^ n), (3 : ℝ) ^ (n - m) * |c Y'| := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Y' _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, fib_card n m hmn, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  have hA : (0 : ℝ) ≤ (3 : ℝ) ^ m / 3 ^ n := by positivity
  unfold Osc
  calc _ ≤ ∑ Y : ZMod (3 ^ n), (|c Y| + (3 : ℝ) ^ m / 3 ^ n *
        ∑ Y' ∈ univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), |c Y'|) := by
        refine Finset.sum_le_sum (fun Y _ => ?_)
        refine le_trans (abs_sub _ _) (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hA]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hA
    _ = 2 * ∑ Y, |c Y| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hswap, ← Finset.mul_sum, ← mul_assoc, hk]
        ring

/-- Item 7d, usable form: if on the bad frequencies `|ĉ| ≤ β |ν̂|`, then
`Osc ≤ β · (3^n Σ ν²)^{1/2}` (Plancherel for `ν`). -/
theorem osc_le_factor (n m : ℕ) (hmn : m ≤ n) (c ν : ZMod (3 ^ n) → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ ξ : ZMod (3 ^ n), ¬ 3 ^ (n - m) ∣ ξ.val →
      ‖fc (fun Y => ((c Y : ℝ) : ℂ)) ξ‖ ≤ β * ‖fc (fun Y => ((ν Y : ℝ) : ℂ)) ξ‖) :
    Osc m n c ≤ β * Real.sqrt ((3 : ℝ) ^ n * ∑ Y, ν Y ^ 2) := by
  refine le_trans (osc_le_fourier n m hmn c) ?_
  have hpar := parseval (3 ^ n) (fun Y => ((ν Y : ℝ) : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Nat.cast_pow, Nat.cast_ofNat] at hpar
  rw [← hpar, ← Real.sqrt_sq hβ, ← Real.sqrt_mul (sq_nonneg β)]
  apply Real.sqrt_le_sqrt
  calc _ ≤ ∑ ξ ∈ univ.filter (fun ξ : ZMod (3 ^ n) => ¬ 3 ^ (n - m) ∣ ξ.val),
          β ^ 2 * ‖fc (fun Y => ((ν Y : ℝ) : ℂ)) ξ‖ ^ 2 := by
        refine Finset.sum_le_sum (fun ξ hξ => ?_)
        have := h ξ (Finset.mem_filter.1 hξ).2
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ ≤ ∑ ξ, β ^ 2 * ‖fc (fun Y => ((ν Y : ℝ) : ℂ)) ξ‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = β ^ 2 * ∑ ξ, ‖fc (fun Y => ((ν Y : ℝ) : ℂ)) ξ‖ ^ 2 := by rw [Finset.mul_sum]

/-- Bridge: the Fourier coefficient of `mu` is the characteristic sum `chi` (Tao (1.28)). -/
lemma fc_mu (n K : ℕ) (ξ : ℤ) :
    fc (fun Y => ((mu n K Y : ℝ) : ℂ)) (ξ : ZMod (3 ^ n)) = chi n K ξ := by
  rw [chi_eq]
  unfold fc mu
  push_cast
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (Box n K) (fun w => syrZ n (padv w))
    (fun w => ((1 : ℂ) / 2) ^ (∑ i, w i) * ZMod.stdAddChar (-(ξ : ZMod (3 ^ n)) * syrZ n (padv w)))]
  refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun w hw => ?_))
  rw [(Finset.mem_filter.1 hw).2, neg_mul]

end Four


/-! Item 7e (S8): factorisation of the Fourier coefficient on a first-block event (Tao Sec. 6). -/

section Fact
open Finset
open Classical

local instance neZeroPow3f (n : ℕ) : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩

lemma ps_eq_sum (a : ℕ → ℕ) (n : ℕ) : ps a n = ∑ j ∈ Finset.range n, a j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ps_succ, ih, Finset.sum_range_succ]

lemma ps_padv {k : ℕ} (u : Fin k → ℕ) : ps (padv u) k = ∑ i, u i := by
  rw [ps_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [padv, i.isLt]

/-- Left / right blocks of a tuple of length `k + q`. -/
def lft {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin k → ℕ := fun i => w (Fin.castAdd q i)
def rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin q → ℕ := fun i => w (Fin.natAdd k i)

lemma padv_lft {k q : ℕ} (w : Fin (k + q) → ℕ) (i : ℕ) (hi : i < k) :
    padv w i = padv (lft w) i := by
  unfold padv lft
  rw [dif_pos (by omega : i < k + q), dif_pos hi]
  rfl

lemma padv_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) (i : ℕ) (hi : i < q) :
    padv w (k + i) = padv (rgt w) i := by
  unfold padv rgt
  rw [dif_pos (by omega : k + i < k + q), dif_pos hi]
  rfl

lemma mem_Box_iff {k q K : ℕ} (w : Fin (k + q) → ℕ) :
    w ∈ Box (k + q) K ↔ lft w ∈ Box k K ∧ rgt w ∈ Box q K := by
  simp only [Box, Fintype.mem_piFinset, lft, rgt]
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.addCases with
    | left j => exact h1 j
    | right j => exact h2 j

lemma lft_append {k q : ℕ} (u : Fin k → ℕ) (v : Fin q → ℕ) : lft (Fin.append u v) = u := by
  funext i; simp [lft]

lemma rgt_append {k q : ℕ} (u : Fin k → ℕ) (v : Fin q → ℕ) : rgt (Fin.append u v) = v := by
  funext i; simp [rgt]

lemma append_lft_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin.append (lft w) (rgt w) = w :=
  Fin.append_castAdd_natAdd

lemma sum_lft_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : ∑ i, w i = ∑ i, lft w i + ∑ i, rgt w i :=
  Fin.sum_univ_add w

/-- Tao (1.5) on tuples: `syr_{k+q}(w) = syr_k(u) + 3^k 2^{-|u|} syr_q(v)` for `w = (u, v)`. -/
lemma syrZ_lr {k q : ℕ} (w : Fin (k + q) → ℕ) :
    syrZ (k + q) (padv w) = (Fnat (padv (lft w)) k : ZMod (3 ^ (k + q))) *
        ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (lft w)) k +
      3 ^ k * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (lft w)) k *
        ((Fnat (padv (rgt w)) q : ZMod (3 ^ (k + q))) *
          ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (rgt w)) q) := by
  rw [syrZ_split (padv w) k q,
    Fnat_congr (padv w) (padv (lft w)) k (fun i hi => padv_lft w i hi),
    ps_congr (padv w) (padv (lft w)) k (fun i hi => padv_lft w i hi),
    Fnat_congr (fun i => padv w (k + i)) (padv (rgt w)) q (fun i hi => padv_rgt w i hi),
    ps_congr (fun i => padv w (k + i)) (padv (rgt w)) q (fun i hi => padv_rgt w i hi)]

/-- The second-block character sum (frequency already multiplied by `3^k 2^{-l}`). -/
noncomputable def sec2 (k q K l : ℕ) (ξ : ZMod (3 ^ (k + q))) : ℂ :=
  ∑ v ∈ Box q K, ((1 : ℂ) / 2) ^ (∑ i, v i) *
    ZMod.stdAddChar (-(ξ * (3 ^ k * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l *
      ((Fnat (padv v) q : ZMod (3 ^ (k + q))) * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv v) q))))

/-- Character sum over a first-block event splits as (first block) x (second block). -/
theorem charsum_split (k q K l : ℕ) (P : (Fin k → ℕ) → Prop) (ξ : ZMod (3 ^ (k + q))) :
    ∑ w ∈ (Box (k + q) K).filter (fun w => P (lft w) ∧ ps (padv (lft w)) k = l),
        ((1 : ℂ) / 2) ^ (∑ i, w i) * ZMod.stdAddChar (-(ξ * syrZ (k + q) (padv w))) =
      (∑ u ∈ (Box k K).filter (fun u => P u ∧ ps (padv u) k = l),
        ((1 : ℂ) / 2) ^ (∑ i, u i) *
          ZMod.stdAddChar (-(ξ * ((Fnat (padv u) k : ZMod (3 ^ (k + q))) *
            ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l)))) * sec2 k q K l ξ := by
  unfold sec2
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_product] at hw ⊢
    rw [mem_Box_iff] at hw
    exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    rw [mem_Box_iff, lft_append, rgt_append]
    exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
  · intro w _; simp [append_lft_rgt]
  · intro p _; simp [lft_append, rgt_append]
  · intro w hw
    simp only [Finset.mem_filter] at hw
    rw [syrZ_lr, hw.2.2, sum_lft_rgt w, pow_add ((1 : ℂ) / 2), mul_add ξ, neg_add,
      AddChar.map_add_eq_mul]
    ring

/-- Fourier coefficient of a fibre-sum function. -/
lemma fc_fiber {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (f : ι → ZMod N) (r : ι → ℝ)
    (ξ : ZMod N) :
    fc (fun Y => ((∑ w ∈ S.filter (fun w => f w = Y), r w : ℝ) : ℂ)) ξ =
      ∑ w ∈ S, (r w : ℂ) * ZMod.stdAddChar (-(ξ * f w)) := by
  unfold fc
  push_cast
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise S f (fun w => (r w : ℂ) * ZMod.stdAddChar (-(ξ * f w)))]
  refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun w hw => ?_))
  rw [(Finset.mem_filter.1 hw).2]

/-- `c_{k,l}`: the distribution of `syr_{k+q}` restricted to the first-block event. -/
noncomputable def cE (k q K l : ℕ) (P : (Fin k → ℕ) → Prop) (Y : ZMod (3 ^ (k + q))) : ℝ :=
  ∑ w ∈ ((Box (k + q) K).filter (fun w => P (lft w) ∧ ps (padv (lft w)) k = l)).filter
      (fun w => syrZ (k + q) (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)

/-- `ν_{k,l}`: the first-block offsets `syr_k(u) = Fnat u · 2^{-l}` on the event. -/
noncomputable def nuE (k q K l : ℕ) (P : (Fin k → ℕ) → Prop) (Y : ZMod (3 ^ (k + q))) : ℝ :=
  ∑ u ∈ ((Box k K).filter (fun u => P u ∧ ps (padv u) k = l)).filter
      (fun u => (Fnat (padv u) k : ZMod (3 ^ (k + q))) * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l = Y),
    ((1 : ℝ) / 2) ^ (∑ i, u i)

theorem fc_cE_eq (k q K l : ℕ) (P : (Fin k → ℕ) → Prop) (ξ : ZMod (3 ^ (k + q))) :
    fc (fun Y => ((cE k q K l P Y : ℝ) : ℂ)) ξ =
      fc (fun Y => ((nuE k q K l P Y : ℝ) : ℂ)) ξ * sec2 k q K l ξ := by
  unfold cE nuE
  rw [fc_fiber, fc_fiber]
  simp only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact charsum_split k q K l P ξ

lemma castHom_two_inv (k q : ℕ) :
    ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
      ((2 : ZMod (3 ^ (k + q)))⁻¹) = (2 : ZMod (3 ^ q))⁻¹ := by
  set φ := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
  have h := congrArg φ (two_mul_inv (k + q))
  rw [map_mul, map_one, map_ofNat] at h
  calc φ (2 : ZMod (3 ^ (k + q)))⁻¹
        = φ (2 : ZMod (3 ^ (k + q)))⁻¹ * (2 * (2 : ZMod (3 ^ q))⁻¹) := by
          rw [two_mul_inv, mul_one]
    _ = (2 * φ (2 : ZMod (3 ^ (k + q)))⁻¹) * (2 : ZMod (3 ^ q))⁻¹ := by ring
    _ = (2 : ZMod (3 ^ q))⁻¹ := by rw [h, one_mul]

lemma stdAddChar_three_pow_mul (k q : ℕ) (x : ZMod (3 ^ (k + q))) :
    (ZMod.stdAddChar ((3 : ZMod (3 ^ (k + q))) ^ k * x) : ℂ) =
      ZMod.stdAddChar (((x.val : ℤ)) : ZMod (3 ^ q)) := by
  have h1 : (3 : ZMod (3 ^ (k + q))) ^ k * x =
      (((3 ^ k * x.val : ℕ) : ℤ) : ZMod (3 ^ (k + q))) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add (3 : ℂ)]
  field_simp

/-- The second block is the truncated characteristic sum `chi q K` at the frequency
`ξ 2^{-l} mod 3^q` (the factor `3^k` kills the top `k` digits). -/
theorem sec2_eq_chi (k q K l : ℕ) (ξ : ZMod (3 ^ (k + q))) :
    sec2 k q K l ξ = chi q K ((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
      (ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l)).val : ℤ) := by
  rw [chi_eq]
  unfold sec2
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  set φ := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
  have key : -(ξ * (3 ^ k * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l *
      ((Fnat (padv v) q : ZMod (3 ^ (k + q))) * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv v) q))) =
      (3 : ZMod (3 ^ (k + q))) ^ k * (-(ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l *
        ((Fnat (padv v) q : ZMod (3 ^ (k + q))) *
          ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv v) q))) := by
    ring
  rw [key, stdAddChar_three_pow_mul]
  congr 1
  rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ← ZMod.cast_eq_val,
    ← ZMod.castHom_apply (h := pow_dvd_pow 3 (Nat.le_add_left q k))]
  unfold syrZ
  simp only [map_neg, map_mul, map_pow, map_natCast, castHom_two_inv, φ]
  ring

theorem norm_fc_cE (k q K l : ℕ) (P : (Fin k → ℕ) → Prop) (ξ : ZMod (3 ^ (k + q))) :
    ‖fc (fun Y => ((cE k q K l P Y : ℝ) : ℂ)) ξ‖ =
      ‖fc (fun Y => ((nuE k q K l P Y : ℝ) : ℂ)) ξ‖ *
        ‖chi q K ((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
          (ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l)).val : ℤ)‖ := by
  rw [fc_cE_eq, norm_mul, sec2_eq_chi]

end Fact


/-! Item 7f (S8): `L²` size of the first-block offsets on the event (Tao Lemma 6.2 / Cor 6.3 step). -/

section Fsq
open Finset
open Classical

local instance neZeroPow3g (n : ℕ) : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩

lemma padv_inj {k : ℕ} (u u' : Fin k → ℕ) (h : ∀ i < k, padv u i = padv u' i) : u = u' := by
  funext i
  have := h i.val i.isLt
  simpa [padv, i.isLt] using this

lemma mem_Box_pos {k K : ℕ} {u : Fin k → ℕ} (hu : u ∈ Box k K) : ∀ i < k, 1 ≤ padv u i := by
  intro i hi
  simp only [Box, Fintype.mem_piFinset, Finset.mem_Icc] at hu
  simp only [padv, dif_pos hi]
  exact (hu ⟨i, hi⟩).1

/-- Item 7f: if the first-block offsets are below `3^(k+q)` on the event, the fibres of `nuE` have at
most one element (Lemma 6.2), so `Σ ν² = 2^{-l} · P(event)`. -/
theorem nuE_sq (k q K l : ℕ) (P : (Fin k → ℕ) → Prop)
    (hlt : ∀ u ∈ (Box k K).filter (fun u => P u ∧ ps (padv u) k = l),
      Fnat (padv u) k < 3 ^ (k + q)) :
    ∑ Y, nuE k q K l P Y ^ 2 = ((1 : ℝ) / 2) ^ l *
      ∑ u ∈ (Box k K).filter (fun u => P u ∧ ps (padv u) k = l), ((1 : ℝ) / 2) ^ (∑ i, u i) := by
  set S := (Box k K).filter (fun u => P u ∧ ps (padv u) k = l) with hS
  set f : (Fin k → ℕ) → ZMod (3 ^ (k + q)) :=
    fun u => (Fnat (padv u) k : ZMod (3 ^ (k + q))) * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l with hf
  have h1 : (2 : ZMod (3 ^ (k + q))) ^ l * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l = 1 := by
    rw [← mul_pow, two_mul_inv, one_pow]
  have hinj : ∀ u ∈ S, ∀ u' ∈ S, f u = f u' → u = u' := by
    intro u hu u' hu' he
    have hu2 := Finset.mem_filter.1 hu
    have hu2' := Finset.mem_filter.1 hu'
    simp only [hf] at he
    have h2 : (Fnat (padv u) k : ZMod (3 ^ (k + q))) = (Fnat (padv u') k : ZMod (3 ^ (k + q))) := by
      linear_combination (2 : ZMod (3 ^ (k + q))) ^ l * he -
        ((Fnat (padv u) k : ZMod (3 ^ (k + q))) - (Fnat (padv u') k : ZMod (3 ^ (k + q)))) * h1
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt u hu),
      Nat.mod_eq_of_lt (hlt u' hu')] at h2
    exact padv_inj u u' (Fnat_inj _ _ k (mem_Box_pos hu2.1) (mem_Box_pos hu2'.1)
      (hu2.2.2.trans hu2'.2.2.symm) h2)
  have hfib : ∀ Y, nuE k q K l P Y ^ 2 =
      ∑ u ∈ S.filter (fun u => f u = Y), (((1 : ℝ) / 2) ^ (∑ i, u i)) ^ 2 := by
    intro Y
    unfold nuE
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.sum_eq_single u]
    · ring
    · intro u' hu' hne
      exfalso; apply hne
      have a := Finset.mem_filter.1 hu
      have b := Finset.mem_filter.1 hu'
      exact (hinj u a.1 u' b.1 (a.2.trans b.2.symm)).symm
    · intro h; exact absurd hu h
  simp_rw [hfib]
  rw [Finset.sum_fiberwise S f (fun u => (((1 : ℝ) / 2) ^ (∑ i, u i)) ^ 2), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hl : ∑ i, u i = l := by rw [← ps_padv]; exact (Finset.mem_filter.1 hu).2.2
  rw [sq]; nth_rewrite 1 [hl]; ring

end Fsq


/-! Item 7h (S9): `chi (k+j) K (3^j η) = chi k K η · (mass of Box j K)`, hence
`‖chi (k+j) K (3^j η)‖ ≤ ‖chi k K η‖` (the factor `3^j` kills the last `j` digits). -/
section Red7h
open Finset
open Classical

lemma castHom_two_inv_gen {a b : ℕ} (h : 3 ^ a ∣ 3 ^ b) :
    ZMod.castHom h (ZMod (3 ^ a)) ((2 : ZMod (3 ^ b))⁻¹) = (2 : ZMod (3 ^ a))⁻¹ := by
  set φ := ZMod.castHom h (ZMod (3 ^ a))
  have h2 := congrArg φ (two_mul_inv b)
  rw [map_mul, map_one, map_ofNat] at h2
  calc φ (2 : ZMod (3 ^ b))⁻¹
        = φ (2 : ZMod (3 ^ b))⁻¹ * (2 * (2 : ZMod (3 ^ a))⁻¹) := by
          rw [two_mul_inv, mul_one]
    _ = (2 * φ (2 : ZMod (3 ^ b))⁻¹) * (2 : ZMod (3 ^ a))⁻¹ := by ring
    _ = (2 : ZMod (3 ^ a))⁻¹ := by rw [h2, one_mul]

lemma stdAddChar_three_pow_mul' (k j : ℕ) (x : ZMod (3 ^ (k + j))) :
    (ZMod.stdAddChar ((3 : ZMod (3 ^ (k + j))) ^ j * x) : ℂ) =
      ZMod.stdAddChar (((x.val : ℤ)) : ZMod (3 ^ k)) := by
  have h1 : (3 : ZMod (3 ^ (k + j))) ^ j * x =
      (((3 ^ j * x.val : ℕ) : ℤ) : ZMod (3 ^ (k + j))) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add (3 : ℂ)]
  field_simp

lemma three_pow_self_zmod (n : ℕ) : (3 : ZMod (3 ^ n)) ^ n = 0 := by
  have h := ZMod.natCast_self (3 ^ n)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

theorem chi_three_pow (k j K : ℕ) (η : ℤ) :
    chi (k + j) K (3 ^ j * η) =
      chi k K η * ∑ v ∈ Box j K, ((1 : ℂ) / 2) ^ (∑ i, v i) := by
  rw [chi_eq, chi_eq, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_product] at hw ⊢
    exact (mem_Box_iff w).1 hw
  · intro p hp
    simp only [Finset.mem_product] at hp ⊢
    rw [mem_Box_iff, lft_append, rgt_append]
    exact hp
  · intro w _; simp [append_lft_rgt]
  · intro p _; simp [lft_append, rgt_append]
  · intro w _
    have key : -(((3 ^ j * η : ℤ)) : ZMod (3 ^ (k + j))) * syrZ (k + j) (padv w) =
        (3 : ZMod (3 ^ (k + j))) ^ j * (-((η : ZMod (3 ^ (k + j)))) *
          ((Fnat (padv (lft w)) k : ZMod (3 ^ (k + j))) *
            ((2 : ZMod (3 ^ (k + j)))⁻¹) ^ ps (padv (lft w)) k)) := by
      rw [syrZ_lr]
      have h0 : (3 : ZMod (3 ^ (k + j))) ^ k * 3 ^ j = 0 := by
        rw [← pow_add]; exact three_pow_self_zmod _
      push_cast
      linear_combination (-(η : ZMod (3 ^ (k + j))) *
        ((2 : ZMod (3 ^ (k + j)))⁻¹) ^ ps (padv (lft w)) k *
        ((Fnat (padv (rgt w)) j : ZMod (3 ^ (k + j))) *
          ((2 : ZMod (3 ^ (k + j)))⁻¹) ^ ps (padv (rgt w)) j)) * h0
    have hc : (((-((η : ZMod (3 ^ (k + j)))) *
          ((Fnat (padv (lft w)) k : ZMod (3 ^ (k + j))) *
            ((2 : ZMod (3 ^ (k + j)))⁻¹) ^ ps (padv (lft w)) k)).val : ℤ) : ZMod (3 ^ k)) =
        -(η : ZMod (3 ^ k)) * syrZ k (padv (lft w)) := by
      rw [Int.cast_natCast, ← ZMod.cast_eq_val,
        ← ZMod.castHom_apply (h := pow_dvd_pow 3 (Nat.le_add_right k j))]
      unfold syrZ
      simp only [map_neg, map_mul, map_pow, map_natCast, map_intCast, castHom_two_inv_gen]
    rw [key, stdAddChar_three_pow_mul', hc, sum_lft_rgt w, pow_add ((1 : ℂ) / 2)]
    ring

lemma box_mass_le (j K : ℕ) : ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) ≤ 1 := by
  have h := box_gen j K 1
  simp only [one_pow, mul_one] at h
  rw [h]
  have hg := geom_Icc_le ((1 : ℝ) / 2) (by norm_num) (by norm_num) K
  have hg' : ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a ≤ 1 := by
    have : (1 : ℝ) / 2 / (1 - 1 / 2) = 1 := by norm_num
    linarith
  have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a := by positivity
  exact pow_le_one₀ h0 hg'

theorem norm_chi_three_pow_le (k j K : ℕ) (η : ℤ) :
    ‖chi (k + j) K (3 ^ j * η)‖ ≤ ‖chi k K η‖ := by
  rw [chi_three_pow, norm_mul]
  have hm : ‖∑ v ∈ Box j K, ((1 : ℂ) / 2) ^ (∑ i, v i)‖ ≤ 1 := by
    have : ∑ v ∈ Box j K, ((1 : ℂ) / 2) ^ (∑ i, v i) =
        ((∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact box_mass_le j K
  calc ‖chi k K η‖ * ‖∑ v ∈ Box j K, ((1 : ℂ) / 2) ^ (∑ i, v i)‖ ≤ ‖chi k K η‖ * 1 :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = ‖chi k K η‖ := mul_one _

end Red7h

/-! Item 7i structural part (S9): 3-adic reduction `red`, fibre sums `proj`, the telescoping
inequality `Osc m n ≤ Osc m' n + Osc m m' (proj m' n ·)` and the consistency of `mu`
(Tao (1.23)): `proj m (m+j) (mu (m+j) K) = mass_j · mu m K`. -/
section Tele
open Finset
open Classical

def red (m n : ℕ) (Y : ZMod (3 ^ n)) : ZMod (3 ^ m) := (Y.val : ZMod (3 ^ m))

lemma red_val (m n : ℕ) (Y : ZMod (3 ^ n)) : (red m n Y).val = Y.val % 3 ^ m := by
  unfold red; rw [ZMod.val_natCast]

lemma red_eq_iff (m n : ℕ) (Y Y' : ZMod (3 ^ n)) :
    red m n Y' = red m n Y ↔ Y'.val % 3 ^ m = Y.val % 3 ^ m := by
  rw [← red_val, ← red_val]
  exact ⟨fun h => by rw [h], fun h => ZMod.val_injective _ h⟩

lemma red_red (m m' n : ℕ) (h : m ≤ m') (Y : ZMod (3 ^ n)) :
    red m m' (red m' n Y) = red m n Y := by
  apply ZMod.val_injective
  simp only [red_val]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 3 h)

noncomputable def proj (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) (Z : ZMod (3 ^ m)) : ℝ :=
  ∑ Y ∈ univ.filter (fun Y => red m n Y = Z), c Y

lemma Osc_eq (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) :
    Osc m n c = ∑ Y, |c Y - (3 : ℝ) ^ m / 3 ^ n * proj m n c (red m n Y)| := by
  unfold Osc proj
  refine sum_congr rfl (fun Y _ => ?_)
  rw [filter_congr (fun Y' _ => (red_eq_iff m n Y Y').symm)]

lemma proj_proj (m m' n : ℕ) (h : m ≤ m') (c : ZMod (3 ^ n) → ℝ) (Z : ZMod (3 ^ m)) :
    proj m m' (proj m' n c) Z = proj m n c Z := by
  unfold proj
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun Y => red m n Y = Z))
    (t := univ.filter (fun Z' => red m m' Z' = Z)) (g := red m' n)
    (by intro Y hY; simp only [mem_filter, mem_univ, true_and] at hY ⊢; rw [red_red m m' n h, hY])]
  refine sum_congr rfl (fun Z' hZ' => ?_)
  rw [filter_filter]
  refine sum_congr (filter_congr (fun Y _ => ?_)) (fun _ _ => rfl)
  simp only [mem_filter, mem_univ, true_and] at hZ'
  constructor
  · intro hY; exact ⟨by rw [← red_red m m' n h, hY, hZ'], hY⟩
  · rintro ⟨_, hY⟩; exact hY

lemma sum_red (m n : ℕ) (h : m ≤ n) (G : ZMod (3 ^ m) → ℝ) :
    ∑ Y : ZMod (3 ^ n), G (red m n Y) = (3 : ℝ) ^ (n - m) * ∑ Z, G Z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := red m n)
    (fun _ _ => mem_univ _), mul_sum]
  refine sum_congr rfl (fun Z _ => ?_)
  rw [sum_congr rfl (fun Y hY => by rw [(mem_filter.1 hY).2])]
  have hZ : Z.val < 3 ^ n := lt_of_lt_of_le (ZMod.val_lt Z) (Nat.pow_le_pow_right (by norm_num) h)
  have hY' : ((Z.val : ZMod (3 ^ n))).val % 3 ^ m = Z.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hZ, Nat.mod_eq_of_lt (ZMod.val_lt Z)]
  have hc : univ.filter (fun Y : ZMod (3 ^ n) => red m n Y = Z) =
      univ.filter (fun Y => ((Z.val : ZMod (3 ^ n))).val % 3 ^ m = Y.val % 3 ^ m) :=
    filter_congr (fun Y _ => by
      rw [hY', ← red_val]
      exact ⟨fun e => by rw [e], fun e => (ZMod.val_injective _ e).symm⟩)
  rw [sum_const, nsmul_eq_mul, hc, fib_card n m h]
  push_cast
  ring

lemma Osc_nonneg (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : 0 ≤ Osc m n c := by
  unfold Osc; exact sum_nonneg (fun _ _ => abs_nonneg _)

theorem Osc_tele (m m' n : ℕ) (h1 : m ≤ m') (h2 : m' ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    Osc m n c ≤ Osc m' n c + Osc m m' (proj m' n c) := by
  rw [Osc_eq, Osc_eq, Osc_eq]
  have hb : (0 : ℝ) ≤ (3 : ℝ) ^ m' / 3 ^ n := by positivity
  have had : (3 : ℝ) ^ m / 3 ^ n = (3 : ℝ) ^ m' / 3 ^ n * ((3 : ℝ) ^ m / 3 ^ m') := by
    rw [div_mul_div_comm, mul_comm ((3 : ℝ) ^ m') ((3 : ℝ) ^ m),
      mul_div_mul_right _ _ (by positivity : (3 : ℝ) ^ m' ≠ 0)]
  have hk : (3 : ℝ) ^ m' / 3 ^ n * 3 ^ (n - m') = 1 := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_cancel' h2, div_self (by positivity)]
  have hs := sum_red m' n h2 (fun Z => |proj m' n c Z - (3 : ℝ) ^ m / 3 ^ m' *
    proj m m' (proj m' n c) (red m m' Z)|)
  beta_reduce at hs
  calc ∑ Y, |c Y - (3 : ℝ) ^ m / 3 ^ n * proj m n c (red m n Y)|
      ≤ ∑ Y, (|c Y - (3 : ℝ) ^ m' / 3 ^ n * proj m' n c (red m' n Y)| +
          (3 : ℝ) ^ m' / 3 ^ n * |proj m' n c (red m' n Y) - (3 : ℝ) ^ m / 3 ^ m' *
            proj m m' (proj m' n c) (red m m' (red m' n Y))|) := by
        refine sum_le_sum (fun Y _ => ?_)
        rw [red_red m m' n h1, proj_proj m m' n h1, had]
        calc _ = |(c Y - (3 : ℝ) ^ m' / 3 ^ n * proj m' n c (red m' n Y)) +
              (3 : ℝ) ^ m' / 3 ^ n * (proj m' n c (red m' n Y) - (3 : ℝ) ^ m / 3 ^ m' *
                proj m n c (red m n Y))| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hb]
    _ = _ := by
        rw [sum_add_distrib, ← mul_sum, hs, ← mul_assoc, hk, one_mul]

lemma Osc_smul (m n : ℕ) (t : ℝ) (ht : 0 ≤ t) (c : ZMod (3 ^ n) → ℝ) :
    Osc m n (fun Y => t * c Y) = t * Osc m n c := by
  unfold Osc
  rw [mul_sum]
  refine sum_congr rfl (fun Y _ => ?_)
  rw [← Finset.mul_sum, mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg ht]

lemma red_syrZ (m j : ℕ) (w : Fin (m + j) → ℕ) :
    red m (m + j) (syrZ (m + j) (padv w)) = syrZ m (padv (lft w)) := by
  unfold red
  rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := pow_dvd_pow 3 (Nat.le_add_right m j)),
    syrZ_lr]
  unfold syrZ
  simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat, castHom_two_inv_gen,
    three_pow_self_zmod, zero_mul, add_zero]

theorem proj_mu (m j K : ℕ) (Z : ZMod (3 ^ m)) :
    proj m (m + j) (mu (m + j) K) Z = mu m K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) := by
  unfold proj mu
  calc ∑ Y ∈ univ.filter (fun Y => red m (m + j) Y = Z),
        ∑ w ∈ (Box (m + j) K).filter (fun w => syrZ (m + j) (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)
      = ∑ w ∈ (Box (m + j) K).filter (fun w => red m (m + j) (syrZ (m + j) (padv w)) = Z),
          ((1 : ℝ) / 2) ^ (∑ i, w i) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := (Box (m + j) K).filter (fun w => red m (m + j) (syrZ (m + j) (padv w)) = Z))
          (t := univ.filter (fun Y => red m (m + j) Y = Z)) (g := fun w => syrZ (m + j) (padv w))
          (by intro w hw; simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.2)]
        refine sum_congr rfl (fun Y hY => ?_)
        rw [filter_filter]
        refine sum_congr (filter_congr (fun w _ => ?_)) (fun _ _ => rfl)
        simp only [mem_filter, mem_univ, true_and] at hY
        constructor
        · intro hw; exact ⟨by rw [hw]; exact hY, hw⟩
        · rintro ⟨_, hw⟩; exact hw
    _ = _ := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2)
          ?_ ?_ ?_ ?_ ?_
        · intro w hw
          simp only [mem_filter, mem_product] at hw ⊢
          rw [mem_Box_iff, red_syrZ] at hw
          exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩
        · intro p hp
          simp only [mem_filter, mem_product] at hp ⊢
          rw [mem_Box_iff, red_syrZ, lft_append, rgt_append]
          exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
        · intro w _; simp [append_lft_rgt]
        · intro p _; simp [lft_append, rgt_append]
        · intro w _; rw [sum_lft_rgt w, pow_add]

lemma box_mass_nonneg (j K : ℕ) : 0 ≤ ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) := by positivity

lemma Osc_proj_mu (m m' j K : ℕ) :
    Osc m m' (proj m' (m' + j) (mu (m' + j) K)) ≤ Osc m m' (mu m' K) := by
  have e : proj m' (m' + j) (mu (m' + j) K) =
      fun Z => (∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i)) * mu m' K Z := by
    funext Z; rw [proj_mu, mul_comm]
  rw [e, Osc_smul _ _ _ (box_mass_nonneg j K)]
  exact mul_le_of_le_one_left (Osc_nonneg _ _ _) (box_mass_le j K)

/-- Tao (6.1) telescoping step for the truncated Syracuse distribution. -/
theorem Osc_mu_tele (m m' j K : ℕ) (h : m ≤ m') :
    Osc m (m' + j) (mu (m' + j) K) ≤ Osc m' (m' + j) (mu (m' + j) K) + Osc m m' (mu m' K) := by
  have := Osc_tele m m' (m' + j) h (Nat.le_add_right m' j) (mu (m' + j) K)
  linarith [Osc_proj_mu m m' j K]

end Tele

/-! Item 7i chain (S9): Tao (6.1) — Proposition 1.14 in the regime `9n ≤ 10m` implies it in general. -/
section Chain
open Finset
open Classical

lemma mu_nonneg (n K : ℕ) (Y : ZMod (3 ^ n)) : 0 ≤ mu n K Y := by
  unfold mu; positivity

lemma sum_mu (n K : ℕ) : ∑ Y, mu n K Y = ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) := by
  unfold mu
  exact Finset.sum_fiberwise (Box n K) (fun w => syrZ n (padv w)) _

lemma Osc_mu_le_two (m n K : ℕ) (h : m ≤ n) : Osc m n (mu n K) ≤ 2 := by
  have h1 := Osc_le_l1 n m h (mu n K)
  have e : ∑ Y, |mu n K Y| = ∑ Y, mu n K Y :=
    sum_congr rfl (fun Y _ => abs_of_nonneg (mu_nonneg n K Y))
  rw [e, sum_mu] at h1
  linarith [box_mass_le n K]

/-- Proposition 1.14 restricted to Tao's regime (6.1) `0.9 n ≤ m ≤ n`. -/
def Prop114w : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → 9 * n ≤ 10 * m → n ≤ K →
    Osc m n (mu n K) ≤ C * (m : ℝ) ^ (-A)

theorem prop114_of_weak (hw : Prop114w) : Prop114 := by
  intro A hA
  obtain ⟨C, hC, hCb⟩ := hw A hA
  set ρ : ℝ := ((20 : ℝ) / 21) ^ A with hρdef
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hA
  have hρ0 : 0 ≤ ρ := by positivity
  set D : ℝ := max (C / (1 - ρ)) (2 * (17 : ℝ) ^ A) with hDdef
  have hD1 : C / (1 - ρ) ≤ D := le_max_left _ _
  have hD2 : 2 * (17 : ℝ) ^ A ≤ D := le_max_right _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD2
  have hCD : C ≤ D * (1 - ρ) := by
    rw [div_le_iff₀ (by linarith)] at hD1; exact hD1
  have hCD' : C ≤ D := by (first | linarith | nlinarith)
  have hweak : ∀ m n K : ℕ, 1 ≤ m → m ≤ n → 9 * n ≤ 10 * m → n ≤ K →
      Osc m n (mu n K) ≤ D * (m : ℝ) ^ (-A) := by
    intro m n K h1 hmn h9 hnK
    have hm0 : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc Osc m n (mu n K) ≤ C * (m : ℝ) ^ (-A) := hCb m n K h1 hmn h9 hnK
      _ ≤ D * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right hCD' hm0
  have hsmall : ∀ m n K : ℕ, 1 ≤ m → m ≤ n → m < 17 → Osc m n (mu n K) ≤ D * (m : ℝ) ^ (-A) := by
    intro m n K h1 hmn h17
    have hmpos : (0 : ℝ) < m := by exact_mod_cast h1
    have hmA : 0 < (m : ℝ) ^ A := Real.rpow_pos_of_pos hmpos _
    have hle : (m : ℝ) ^ A ≤ (17 : ℝ) ^ A :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h17.le) hA.le
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hmA]
    have h2 := Osc_mu_le_two m n K hmn
    have h0 := Osc_nonneg m n (mu n K)
    (first | linarith | nlinarith)
  have key : ∀ d : ℕ, ∀ m n K : ℕ, n - m ≤ d → 1 ≤ m → m ≤ n → n ≤ K →
      Osc m n (mu n K) ≤ D * (m : ℝ) ^ (-A) := by
    intro d
    induction d with
    | zero =>
      intro m n K hd h1 hmn hnK
      exact hweak m n K h1 hmn (by omega) hnK
    | succ d ih =>
      intro m n K hd h1 hmn hnK
      by_cases h17 : m < 17
      · exact hsmall m n K h1 hmn h17
      by_cases h9 : 9 * n ≤ 10 * m
      · exact hweak m n K h1 hmn h9 hnK
      have f1 : m ≤ 10 * m / 9 := by omega
      have f2 : 9 * (10 * m / 9) ≤ 10 * m := by omega
      have f3 : 10 * m / 9 ≤ n := by omega
      have f4 : n - 10 * m / 9 ≤ d := by omega
      have f5 : 21 * m ≤ 20 * (10 * m / 9) := by omega
      have f6 : 1 ≤ 10 * m / 9 := by omega
      generalize 10 * m / 9 = m' at f1 f2 f3 f4 f5 f6
      obtain ⟨j, rfl⟩ : ∃ j, n = m' + j := ⟨n - m', by omega⟩
      have hT := Osc_mu_tele m m' j K f1
      have hI := ih m' (m' + j) K f4 f6 (Nat.le_add_right _ _) hnK
      have hW := hCb m m' K h1 f1 f2 (by omega)
      have hmpos : (0 : ℝ) < m := by exact_mod_cast h1
      have hcast : (21 : ℝ) / 20 * m ≤ m' := by
        have : (21 : ℝ) * m ≤ 20 * m' := by exact_mod_cast f5
        linarith
      have hpow : ((21 : ℝ) / 20 * m) ^ A ≤ (m' : ℝ) ^ A :=
        Real.rpow_le_rpow (by positivity) hcast hA.le
      have hpos : 0 < ((21 : ℝ) / 20 * m) ^ A := Real.rpow_pos_of_pos (by positivity) _
      have hρ' : ρ = (((21 : ℝ) / 20) ^ A)⁻¹ := by
        rw [hρdef, show (20 : ℝ) / 21 = ((21 : ℝ) / 20)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num)]
      have hm' : (m' : ℝ) ^ (-A) ≤ ρ * (m : ℝ) ^ (-A) := by
        rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _), hρ',
          ← mul_inv]
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at hpow hpos
        exact inv_anti₀ hpos hpow
      have hm0 : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc Osc m (m' + j) (mu (m' + j) K)
          ≤ D * (m' : ℝ) ^ (-A) + C * (m : ℝ) ^ (-A) := by linarith
        _ ≤ D * (ρ * (m : ℝ) ^ (-A)) + C * (m : ℝ) ^ (-A) := by
            have := mul_le_mul_of_nonneg_left hm' hDpos.le
            linarith
        _ = (D * ρ + C) * (m : ℝ) ^ (-A) := by ring
        _ ≤ D * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right (by nlinarith) hm0
  refine ⟨D, hDpos, ?_⟩
  intro m n K h1 hmn hnK
  exact key (n - m) m n K le_rfl h1 hmn hnK

end Chain

/-! Item 7f (S9): Tao Cor 6.3 size bound `Fnat < 3^n` on the deviation event. -/
section Cor63

/-- Item 7f analytic core (Tao Cor 6.3, (6.14) per-term bound): with deviation allowance
`C(√((j+1)L) + L)` on the partial sum `s = a_{[1,j+1]}` and `2^l · 2^{0.99 C² L} ≤ 3^n`,
the `j`-th term `3^j 2^{l-s}` of the offset is at most `3^n (19/20)^j / 40`. -/
theorem term_bound (j s l n : ℕ) (hsl : s ≤ l) (C L : ℝ) (hC : 10 ≤ C) (hL : 1 ≤ L)
    (hl : (2 : ℝ) ^ l * (2 : ℝ) ^ ((99 / 100) * C ^ 2 * L) ≤ 3 ^ n)
    (hs : 2 * ((j : ℝ) + 1) ≤ s + C * Real.sqrt (((j : ℝ) + 1) * L) + C * L) :
    (3 : ℝ) ^ j * 2 ^ (l - s) ≤ 3 ^ n * ((19 / 20 : ℝ) ^ j * (1 / 40)) := by
  set t : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3) with htdef
  have ht0 : 0 < t := by positivity
  have ht3 : t ^ 3 = 2 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hq : 3 / 4 * t ≤ 19 / 20 := by
    by_contra hcon
    push Not at hcon
    have h1 : 19 / 15 < t := by linarith
    have h2 : 0 < t - 19 / 15 := by linarith
    (first | linarith [mul_pos h2 h2, mul_pos (mul_pos h2 h2) h2] | nlinarith [mul_pos h2 h2, mul_pos (mul_pos h2 h2) h2])
  have hL0 : 0 < L := by linarith
  have hC0 : 0 < C := by linarith
  have hsq : C * Real.sqrt (((j : ℝ) + 1) * L) ≤ ((j : ℝ) + 1) / 3 + 3 / 4 * C ^ 2 * L := by
    set r := Real.sqrt (((j : ℝ) + 1) * L)
    have hr : r ^ 2 = ((j : ℝ) + 1) * L := Real.sq_sqrt (by positivity)
    have key : 3 * L * (C * r) ≤ 3 * L * (((j : ℝ) + 1) / 3 + 3 / 4 * C ^ 2 * L) := by
      (first | linarith [sq_nonneg (r - 3 / 2 * C * L)] | nlinarith [sq_nonneg (r - 3 / 2 * C * L)])
    exact le_of_mul_le_mul_left key (by positivity)
  have hCL10 : 10 ≤ C * L := by (first | linarith | nlinarith)
  have hCL : 14 ≤ (24 / 100) * C ^ 2 * L - C * L := by
    (first | linarith [mul_nonneg (sub_nonneg.2 hC) (by positivity : (0 : ℝ) ≤ C * L)] | nlinarith [mul_nonneg (sub_nonneg.2 hC) (by positivity : (0 : ℝ) ≤ C * L)])
  have hE : (5 / 3 : ℝ) * j - s - (99 / 100) * C ^ 2 * L ≤ -6 := by (first | linarith | nlinarith)
  have h3 : (3 : ℝ) ^ j = (3 / 4 * t) ^ j * (2 : ℝ) ^ ((5 / 3 : ℝ) * j) := by
    rw [mul_pow, ← Real.rpow_natCast t j, htdef, ← Real.rpow_mul (by norm_num), mul_assoc,
      ← Real.rpow_add (by norm_num)]
    have e : (1 / 3 : ℝ) * j + 5 / 3 * j = ((2 * j : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast, pow_mul, ← mul_pow]
    norm_num
  have h2 : (2 : ℝ) ^ (l - s) = (2 : ℝ) ^ ((l : ℝ) - s) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hsl]
  have hl' : (2 : ℝ) ^ (l : ℝ) ≤ 3 ^ n * (2 : ℝ) ^ (-((99 / 100) * C ^ 2 * L)) := by
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
      Real.rpow_natCast]
    exact hl
  have h64 : (2 : ℝ) ^ (-6 : ℝ) = 1 / 64 := by
    rw [Real.rpow_neg (by norm_num), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  calc (3 : ℝ) ^ j * 2 ^ (l - s)
      = (3 / 4 * t) ^ j * ((2 : ℝ) ^ ((5 / 3 : ℝ) * j - s) * (2 : ℝ) ^ (l : ℝ)) := by
        rw [h3, h2, mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2; ring
    _ ≤ (3 / 4 * t) ^ j * ((2 : ℝ) ^ ((5 / 3 : ℝ) * j - s) *
          (3 ^ n * (2 : ℝ) ^ (-((99 / 100) * C ^ 2 * L)))) := by gcongr
    _ = (3 / 4 * t) ^ j * 3 ^ n * (2 : ℝ) ^ ((5 / 3 : ℝ) * j - s - (99 / 100) * C ^ 2 * L) := by
        rw [sub_eq_add_neg ((5 / 3 : ℝ) * j - s), Real.rpow_add (by norm_num)]; ring
    _ ≤ (19 / 20) ^ j * 3 ^ n * (2 : ℝ) ^ (-6 : ℝ) := by
        have hA : (3 / 4 * t) ^ j ≤ (19 / 20 : ℝ) ^ j := by gcongr
        have hB : (2 : ℝ) ^ ((5 / 3 : ℝ) * j - s - (99 / 100) * C ^ 2 * L) ≤ (2 : ℝ) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
        have h3n : (0 : ℝ) ≤ 3 ^ n := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right hA h3n) hB (by positivity) (by positivity)
    _ ≤ 3 ^ n * ((19 / 20 : ℝ) ^ j * (1 / 40)) := by
        rw [h64]
        have : (0 : ℝ) ≤ (19 / 20) ^ j * 3 ^ n := by positivity
        (first | linarith | nlinarith)


theorem Fnat_lt_of_dev (a : ℕ → ℕ) (k n : ℕ) (C L : ℝ) (hC : 10 ≤ C) (hL : 1 ≤ L)
    (hl : (2 : ℝ) ^ (ps a k) * (2 : ℝ) ^ ((99 / 100) * C ^ 2 * L) ≤ 3 ^ n)
    (hs : ∀ j < k, 2 * ((j : ℝ) + 1) ≤ (ps a (j + 1) : ℝ) +
      C * Real.sqrt (((j : ℝ) + 1) * L) + C * L) :
    Fnat a k < 3 ^ n := by
  have hterm : ∀ j ∈ Finset.range k, (3 : ℝ) ^ j * 2 ^ (ps a k - ps a (j + 1)) ≤
      3 ^ n * ((19 / 20 : ℝ) ^ j * (1 / 40)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact term_bound j (ps a (j + 1)) (ps a k) n (ps_mono a (by omega)) C L hC hL hl (hs j hj)
  have hgeo : ∑ j ∈ Finset.range k, (19 / 20 : ℝ) ^ j ≤ 20 := by
    have h := geom_sum_Ico_le_of_lt_one (x := (19 / 20 : ℝ)) (m := 0) (n := k)
      (by norm_num) (by norm_num)
    rw [← Finset.range_eq_Ico] at h
    norm_num at h
    linarith
  have hR : (Fnat a k : ℝ) < 3 ^ n := by
    unfold Fnat
    push_cast
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    calc ∑ j ∈ Finset.range k, (3 : ℝ) ^ j * 2 ^ (ps a k - ps a (j + 1))
        ≤ ∑ j ∈ Finset.range k, 3 ^ n * ((19 / 20 : ℝ) ^ j * (1 / 40)) := Finset.sum_le_sum hterm
      _ = 3 ^ n * (1 / 40) * ∑ j ∈ Finset.range k, (19 / 20 : ℝ) ^ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ 3 ^ n * (1 / 40) * 20 := by gcongr
      _ < 3 ^ n := by linarith
  exact_mod_cast hR

end Cor63


/-! ## Section Asm7g (session 10): pieces of the 7g assembly `Prop117 -> Prop114w`. -/
section Asm7g
open Finset
open Classical

/-- `3^d ∣ x.val` iff `x` vanishes mod `3^d`. -/
lemma dvd_val_iff_cast {d n : ℕ} (h : 3 ^ d ∣ 3 ^ n) (x : ZMod (3 ^ n)) :
    3 ^ d ∣ x.val ↔ ZMod.castHom h (ZMod (3 ^ d)) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- Multiplying by a power of `2⁻¹` does not change vanishing mod `3^d`. -/
lemma cast_mul_two_inv_pow_ne {d n : ℕ} (h : 3 ^ d ∣ 3 ^ n) (ξ : ZMod (3 ^ n)) (l : ℕ)
    (hξ : ZMod.castHom h (ZMod (3 ^ d)) ξ ≠ 0) :
    ZMod.castHom h (ZMod (3 ^ d)) (ξ * ((2 : ZMod (3 ^ n))⁻¹) ^ l) ≠ 0 := by
  rw [map_mul, map_pow, castHom_two_inv_gen h]
  intro h0
  apply hξ
  have h1 := congrArg (· * (2 : ZMod (3 ^ d)) ^ l) h0
  simp only [zero_mul] at h1
  rw [mul_assoc, ← mul_pow, mul_comm ((2 : ZMod (3 ^ d))⁻¹), two_mul_inv, one_pow,
    mul_one] at h1
  exact h1

/-- Tao Sec 6 (after (6.10)): at a frequency `ξ ∉ 3^{n-m} Z/3^n` the second-block factor is a
characteristic sum `chi r K η` with `3 ∤ η` and `r > q - (n - m)` (via (1.23) = `norm_chi_three_pow_le`). -/
theorem chi_bad_le (k q K l m : ℕ) (hd : k + q - m ≤ q) (β : ℝ)
    (hB : ∀ r : ℕ, q - (k + q - m) < r → r ≤ q → ∀ η : ℤ, ¬ (3 : ℤ) ∣ η → ‖chi r K η‖ ≤ β)
    (ξ : ZMod (3 ^ (k + q))) (hξ : ¬ 3 ^ (k + q - m) ∣ ξ.val) :
    ‖chi q K ((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
          (ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l)).val : ℤ)‖ ≤ β := by
  set d := k + q - m with hd_def
  have hdn : 3 ^ d ∣ 3 ^ (k + q) := pow_dvd_pow 3 (by omega)
  have hdq : 3 ^ d ∣ 3 ^ q := pow_dvd_pow 3 hd
  have h1 : ZMod.castHom hdn (ZMod (3 ^ d)) ξ ≠ 0 := fun h0 =>
    hξ ((dvd_val_iff_cast hdn ξ).2 h0)
  have h2 := cast_mul_two_inv_pow_ne hdn ξ l h1
  set x := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
    (ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l) with hx
  have h3 : ¬ 3 ^ d ∣ x.val := by
    rw [dvd_val_iff_cast hdq, hx, ← RingHom.comp_apply, ZMod.castHom_comp]
    exact h2
  have hv0 : x.val ≠ 0 := by
    intro h0; exact h3 (h0 ▸ dvd_zero _)
  obtain ⟨j, η, hη, hv⟩ := Nat.exists_eq_pow_mul_and_not_dvd hv0 3 (by norm_num)
  have hjd : j < d := by
    by_contra hc
    rw [not_lt] at hc
    exact h3 (hv ▸ Dvd.dvd.mul_right (pow_dvd_pow 3 hc) _)
  rw [hv]
  obtain ⟨r, hr⟩ : ∃ r, q = r + j := ⟨q - j, by omega⟩
  have hc := norm_chi_three_pow_le r j K (η : ℤ)
  rw [← hr] at hc
  have hη' : ¬ (3 : ℤ) ∣ (η : ℤ) := by exact_mod_cast hη
  push_cast
  exact le_trans hc (hB r (by omega) (by omega) η hη')

/-- Per-piece estimate (Tao (6.10)-(6.11)): Plancherel + factorisation + Renyi bound. -/
theorem osc_cE_le (k q K l m : ℕ) (P : (Fin k → ℕ) → Prop) (hm : m ≤ k + q) (β : ℝ)
    (hβ : 0 ≤ β)
    (hchi : ∀ ξ : ZMod (3 ^ (k + q)), ¬ 3 ^ (k + q - m) ∣ ξ.val →
      ‖chi q K ((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q k)) (ZMod (3 ^ q))
          (ξ * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ l)).val : ℤ)‖ ≤ β)
    (hlt : ∀ u ∈ (Box k K).filter (fun u => P u ∧ ps (padv u) k = l),
      Fnat (padv u) k < 3 ^ (k + q)) :
    Osc m (k + q) (cE k q K l P) ≤ β * Real.sqrt ((3 : ℝ) ^ (k + q) * ((1 : ℝ) / 2) ^ l) := by
  have hO := osc_le_factor (k + q) m hm (cE k q K l P) (nuE k q K l P) β hβ (by
    intro ξ hξ
    rw [norm_fc_cE, mul_comm]
    exact mul_le_mul_of_nonneg_right (hchi ξ hξ) (norm_nonneg _))
  refine le_trans hO (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hβ)
  rw [nuE_sq k q K l P hlt]
  have hmass : ∑ u ∈ (Box k K).filter (fun u => P u ∧ ps (padv u) k = l),
      ((1 : ℝ) / 2) ^ (∑ i, u i) ≤ 1 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)) (box_mass_le k K)
  have h2 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ l := by positivity
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (k + q) := by positivity
  calc (3 : ℝ) ^ (k + q) * (((1 : ℝ) / 2) ^ l * _)
      ≤ (3 : ℝ) ^ (k + q) * (((1 : ℝ) / 2) ^ l * 1) := by gcongr
    _ = (3 : ℝ) ^ (k + q) * ((1 : ℝ) / 2) ^ l := by ring

end Asm7g


/-! ## Section Dev7g (session 10): the deviation event `E` of Tao (6.2)-(6.3), prefix form. -/
section Dev7g
open Finset
open Classical

lemma sum_filter_or_le {α : Type*} (S : Finset α) (B₁ B₂ : α → Prop) [DecidablePred B₁]
    [DecidablePred B₂] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ S.filter (fun a => B₁ a ∨ B₂ a), f a ≤
      ∑ a ∈ S.filter B₁, f a + ∑ a ∈ S.filter B₂, f a := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have := hf a
  by_cases h1 : B₁ a <;> by_cases h2 : B₂ a <;> simp [h1, h2] <;> linarith

lemma sum_filter_exists_le {α : Type*} (S : Finset α) (J : Finset ℕ) (B : ℕ → α → Prop)
    (d1 : ∀ j, DecidablePred (B j)) (d2 : DecidablePred (fun a => ∃ j ∈ J, B j a))
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ @Finset.filter α (fun a => ∃ j ∈ J, B j a) d2 S, f a ≤
      ∑ j ∈ J, ∑ a ∈ @Finset.filter α (B j) (d1 j) S, f a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have hnn : ∀ j ∈ J, 0 ≤ (if B j a then f a else 0) := fun j _ => by
    split_ifs
    · exact hf a
    · exact le_refl 0
  split_ifs with h
  · obtain ⟨j, hj, hB⟩ := h
    have := Finset.single_le_sum (f := fun j => if B j a then f a else 0) hnn hj
    rw [if_pos hB] at this
    exact this
  · exact Finset.sum_nonneg hnn

/-- Prefix marginal: an event on `ps a j` has the same `Box`-mass in length `j + q` as in length `j`
(up to the factor `mass(Box q K) ≤ 1`). -/
lemma prefix_marg (j q K : ℕ) (R : ℕ → Prop) [DecidablePred R] :
    ∑ w ∈ (Box (j + q) K).filter (fun w => R (ps (padv w) j)), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      ∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i) := by
  have hps : ∀ w : Fin (j + q) → ℕ, ps (padv w) j = ∑ i, lft w i := by
    intro w; rw [← ps_padv]; exact ps_congr _ _ _ (fun i hi => padv_lft w i hi)
  have heq : ∑ w ∈ (Box (j + q) K).filter (fun w => R (ps (padv w) j)),
      ((1 : ℝ) / 2) ^ (∑ i, w i) =
      (∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i)) *
        ∑ v ∈ Box q K, ((1 : ℝ) / 2) ^ (∑ i, v i) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hw ⊢
      rw [mem_Box_iff] at hw
      refine ⟨⟨hw.1.1, ?_⟩, hw.1.2⟩
      rw [← hps]; exact hw.2
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
      rw [mem_Box_iff, lft_append, rgt_append, hps, lft_append]
      exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
    · intro w _; simp [append_lft_rgt]
    · intro p _; simp [lft_append, rgt_append]
    · intro w _
      dsimp only
      rw [sum_lft_rgt w, pow_add]
  rw [heq]
  calc _ ≤ (∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i)) * 1 :=
        mul_le_mul_of_nonneg_left (box_mass_le q K)
          (Finset.sum_nonneg (fun _ _ => by positivity))
    _ = _ := mul_one _

lemma prefix_marg' (n K j : ℕ) (hj : j ≤ n) (R : ℕ → Prop) [DecidablePred R] :
    ∑ w ∈ (Box n K).filter (fun w => R (ps (padv w) j)), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      ∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact prefix_marg j q K R

lemma exp_dev_le (j : ℕ) (hj : 1 ≤ j) (C L : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    Real.exp (-((C * (Real.sqrt (j * L) + L)) * min (C * (Real.sqrt (j * L) + L) / j) 1) / 24)
      ≤ Real.exp (-(C * L) / 24) := by
  apply Real.exp_le_exp.2
  set s := Real.sqrt (j * L) with hs_def
  set t := C * (s + L) with ht_def
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have ht : C * L ≤ t := by rw [ht_def]; (first | linarith | nlinarith)
  suffices h : C * L ≤ t * min (t / j) 1 by linarith
  rcases le_total (t / j) 1 with h | h
  · rw [min_eq_left h]
    have hsq : s ^ 2 = j * L := Real.sq_sqrt (by positivity)
    have h1 : C * s ≤ t := by rw [ht_def]; (first | linarith | nlinarith)
    have h2 : (C * s) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : C * L * j ≤ (C * s) ^ 2 := by
      rw [mul_pow, hsq]
      have := mul_nonneg (mul_nonneg (mul_nonneg hC0 hL) (by linarith : (0 : ℝ) ≤ j))
        (sub_nonneg.2 hC)
      (first | linarith | nlinarith)
    rw [show t * (t / j) = t ^ 2 / j by ring, le_div_iff₀ (by linarith)]
    linarith
  · rw [min_eq_right h, mul_one]; exact ht

/-- Tao (6.2): all prefix deviations `|a_{[1,j]} - 2j| ≤ C(√(jL) + L)`, `1 ≤ j ≤ k`. -/
def DevOK (C L : ℝ) (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, |(ps a j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L)

/-- Tao (6.3) (prefix form): `P(¬E) ≤ 2n e^{-CL/24}` via Lemma 2.2 and the union bound. -/
theorem dev_bad_mass (n K : ℕ) (C L : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n), ((1 : ℝ) / 2) ^ (∑ i, w i)
      ≤ 2 * n * Real.exp (-(C * L) / 24) := by
  have hf : ∀ w : Fin n → ℕ, (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, w i) := fun _ => by positivity
  have hsub0 : (Box n K).filter (fun w => ¬ DevOK C L (padv w) n) ⊆
      (Box n K).filter (fun w => ∃ j ∈ Finset.Icc 1 n,
        C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|) := by
    intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have h2 := hw.2
    unfold DevOK at h2
    push_neg at h2
    exact h2
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub0 (fun w _ _ => hf w)) ?_
  set f : (Fin n → ℕ) → ℝ := fun w => ((1 : ℝ) / 2) ^ (∑ i, w i) with hf_def
  refine le_trans (sum_filter_exists_le (Box n K) (Finset.Icc 1 n)
    (fun j w => C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|)
    (fun j => inferInstance) _ f hf) ?_
  have hj : ∀ j ∈ Finset.Icc 1 n,
      ∑ w ∈ (Box n K).filter (fun w =>
        C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|), f w
        ≤ 2 * Real.exp (-(C * L) / 24) := by
    intro j hjm
    rw [Finset.mem_Icc] at hjm
    set t := C * (Real.sqrt (j * L) + L) with ht_def
    have ht0 : 0 ≤ t := by rw [ht_def]; have := Real.sqrt_nonneg (j * L); (first | linarith | nlinarith)
    have hsub : (Box n K).filter (fun w => t < |(ps (padv w) j : ℝ) - 2 * j|) ⊆
        (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ) ∨
          ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t) := by
      intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rcases lt_abs.1 hw.2 with h | h
      · left; linarith
      · right; linarith
    have hsum : ∑ w ∈ (Box n K).filter (fun w => t < |(ps (padv w) j : ℝ) - 2 * j|), f w ≤
        ∑ w ∈ (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ)), f w +
        ∑ w ∈ (Box n K).filter (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t), f w :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hf w))
        (sum_filter_or_le (Box n K)
              (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ))
              (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t) f hf)
    have hu : ∑ w ∈ (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ)),
        f w ≤ Real.exp (-(t * min (t / j) 1) / 24) := by
      exact le_trans (prefix_marg' n K j hjm.2 (fun s => 2 * (j : ℝ) + t ≤ ((s : ℕ) : ℝ)))
        (chernoff_up j K hjm.1 t ht0)
    have hd : ∑ w ∈ (Box n K).filter (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t),
        f w ≤ Real.exp (-(t * min (t / j) 1) / 24) := by
      exact le_trans (prefix_marg' n K j hjm.2 (fun s => ((s : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t))
        (chernoff_down j K hjm.1 t ht0)
    have he := exp_dev_le j hjm.1 C L hC hL
    rw [← ht_def] at he
    linarith
  refine le_trans (Finset.sum_le_sum hj) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp only [Nat.add_sub_cancel]
  linarith

end Dev7g


/-! ## S11: 7g decomposition by the stopping time (Tao (6.4)-(6.9)) -/
section Dec7g
open Finset
open Classical

/-- Stopping-time event on the first block: prefix deviations OK and `ps(k-1) ≤ T < ps k ≤ T + D`. -/
def Qs (C L : ℝ) (T D k : ℕ) (a : ℕ → ℕ) : Prop :=
  DevOK C L a k ∧ ps a (k - 1) ≤ T ∧ T < ps a k ∧ ps a k ≤ T + D

lemma DevOK_congr (C L : ℝ) (a b : ℕ → ℕ) (k : ℕ) (h : ∀ i < k, a i = b i) :
    DevOK C L a k ↔ DevOK C L b k := by
  unfold DevOK
  constructor
  · intro H j hj
    have hjk := (Finset.mem_Icc.1 hj).2
    rw [← ps_congr a b j (fun i hi => h i (by omega))]
    exact H j hj
  · intro H j hj
    have hjk := (Finset.mem_Icc.1 hj).2
    rw [ps_congr a b j (fun i hi => h i (by omega))]
    exact H j hj

lemma Qs_congr (C L : ℝ) (T D k : ℕ) (a b : ℕ → ℕ) (h : ∀ i < k, a i = b i) :
    Qs C L T D k a ↔ Qs C L T D k b := by
  unfold Qs
  rw [DevOK_congr C L a b k h, ps_congr a b k h,
    ps_congr a b (k - 1) (fun i hi => h i (by omega))]

lemma Qs_unique (C L : ℝ) (T D : ℕ) (a : ℕ → ℕ) {k k' : ℕ}
    (h : Qs C L T D k a) (h' : Qs C L T D k' a) : k = k' := by
  rcases h with ⟨-, h1, h2, -⟩
  rcases h' with ⟨-, h1', h2', -⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := ps_mono a (show k ≤ k' - 1 by omega); omega
  · have := ps_mono a (show k' ≤ k - 1 by omega); omega

lemma Qs_exists (C L : ℝ) (T D n : ℕ) (a : ℕ → ℕ) (hdev : DevOK C L a n) (hT : T < ps a n)
    (hD : ∀ j < n, a j ≤ D) : ∃ k ∈ Finset.Icc 1 n, Qs C L T D k a := by
  have hex : ∃ k, T < ps a k := ⟨n, hT⟩
  have hkT : T < ps a (Nat.find hex) := Nat.find_spec hex
  have hkn : Nat.find hex ≤ n := Nat.find_min' hex hT
  have hk1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have h00 : Nat.find hex = 0 := by omega
    rw [h00] at hkT
    simp [ps] at hkT
  have hprev : ps a (Nat.find hex - 1) ≤ T := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  refine ⟨Nat.find hex, Finset.mem_Icc.2 ⟨hk1, hkn⟩, ?_, hprev, hkT, ?_⟩
  · intro j hj
    exact hdev j (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, le_trans (Finset.mem_Icc.1 hj).2 hkn⟩)
  · have h1 : ps a (Nat.find hex) = ps a (Nat.find hex - 1) + a (Nat.find hex - 1) := by
      have := ps_succ a (Nat.find hex - 1)
      rwa [Nat.sub_add_cancel hk1] at this
    have h2 := hD (Nat.find hex - 1) (by omega)
    omega

/-- The piece of `mu n` on the first-block event `Q` with `ps k = l` (Tao's `c_{k,l}`, stated in `n`). -/
noncomputable def dE (n K k l : ℕ) (Q : (ℕ → ℕ) → Prop) (Y : ZMod (3 ^ n)) : ℝ :=
  ∑ w ∈ ((Box n K).filter (fun w => Q (padv w) ∧ ps (padv w) k = l)).filter
      (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)

lemma dE_eq_cE (k q K l : ℕ) (Q : (ℕ → ℕ) → Prop)
    (hQ : ∀ a b : ℕ → ℕ, (∀ i < k, a i = b i) → (Q a ↔ Q b)) :
    dE (k + q) K k l Q = cE k q K l (fun u => Q (padv u)) := by
  funext Y
  unfold dE cE
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext w
  simp only [Finset.mem_filter]
  have h1 : Q (padv w) ↔ Q (padv (lft w)) := hQ _ _ (fun i hi => padv_lft w i hi)
  have h2 : ps (padv w) k = ps (padv (lft w)) k := ps_congr _ _ _ (fun i hi => padv_lft w i hi)
  rw [h1, h2]

/-- Per-piece oscillation bound in `n` (wraps `osc_cE_le` + `chi_bad_le`). -/
theorem osc_dE_le (n k K l m : ℕ) (Q : (ℕ → ℕ) → Prop)
    (hQ : ∀ a b : ℕ → ℕ, (∀ i < k, a i = b i) → (Q a ↔ Q b))
    (hkm : k ≤ m) (hmn : m ≤ n) (β : ℝ) (hβ : 0 ≤ β)
    (hB : ∀ r : ℕ, m - k < r → r ≤ n - k → ∀ η : ℤ, ¬ (3 : ℤ) ∣ η → ‖chi r K η‖ ≤ β)
    (hlt : ∀ u ∈ Box k K, Q (padv u) → Fnat (padv u) k < 3 ^ n) :
    Osc m n (dE n K k l Q) ≤ β * Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ l) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (le_trans hkm hmn)
  rw [dE_eq_cE k q K l Q hQ]
  refine osc_cE_le k q K l m (fun u => Q (padv u)) hmn β hβ ?_ ?_
  · intro ξ hξ
    exact chi_bad_le k q K l m (by omega) β
      (fun r hr1 hr2 η hη => hB r (by omega) (by omega) η hη) ξ hξ
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact hlt u hu.1 hu.2.1

/-- Tao (6.4)-(6.9): `mu = Σ_{k,l} c_{k,l} + (mass off the stopping-time events)`. -/
theorem mu_decomp (n K : ℕ) (C L : ℝ) (T D : ℕ) (Y : ZMod (3 ^ n)) :
    mu n K Y = ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc T (T + D), dE n K k l (Qs C L T D k) Y +
      ∑ w ∈ ((Box n K).filter (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w))).filter
        (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i) := by
  have key : ∀ w ∈ Box n K, (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) =
      ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc T (T + D),
        (if Qs C L T D k (padv w) ∧ ps (padv w) k = l then
          (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) else 0) +
      (if ¬ ∃ k ∈ Icc 1 n, Qs C L T D k (padv w) then
          (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) else 0) := by
    intro w _
    set g := (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) with hg
    by_cases hG : ∃ k ∈ Icc 1 n, Qs C L T D k (padv w)
    · obtain ⟨k0, hk0, hQ0⟩ := hG
      rw [if_neg (not_not.2 ⟨k0, hk0, hQ0⟩), add_zero]
      rw [Finset.sum_eq_single k0]
      · have hl : ps (padv w) k0 ∈ Ioc T (T + D) := Finset.mem_Ioc.2 ⟨hQ0.2.2.1, hQ0.2.2.2⟩
        rw [Finset.sum_eq_single (ps (padv w) k0)]
        · rw [if_pos ⟨hQ0, rfl⟩]
        · intro b _ hb
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hb h.symm
        · intro h; exact absurd hl h
      · intro b _ hb
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [if_neg]
        rintro ⟨h, -⟩
        exact hb (Qs_unique C L T D (padv w) h hQ0)
      · intro h; exact absurd hk0 h
    · rw [if_pos hG]
      have h0 : ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc T (T + D),
          (if Qs C L T D k (padv w) ∧ ps (padv w) k = l then g else 0) = 0 :=
        Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l _ => by
          rw [if_neg]
          rintro ⟨h, -⟩
          exact hG ⟨k, hk, h⟩))
      rw [h0, zero_add]
  have hmu : mu n K Y = ∑ w ∈ Box n K,
      (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) := by
    unfold mu; rw [Finset.sum_filter]
  have hdE : ∀ k l, dE n K k l (Qs C L T D k) Y = ∑ w ∈ Box n K,
      (if Qs C L T D k (padv w) ∧ ps (padv w) k = l then
        (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) else 0) := by
    intro k l; unfold dE; rw [Finset.sum_filter, Finset.sum_filter]
  have hrest : ∑ w ∈ ((Box n K).filter (fun w => ¬ ∃ k ∈ Finset.Icc 1 n,
        Qs C L T D k (padv w))).filter (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)
      = ∑ w ∈ Box n K, (if ¬ ∃ k ∈ Icc 1 n, Qs C L T D k (padv w) then
          (if syrZ n (padv w) = Y then ((1 : ℝ) / 2) ^ (∑ i, w i) else 0) else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
  rw [hmu, hrest]
  simp only [hdE]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm), Finset.sum_comm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => by convert key w hw)

/-- `Osc` is subadditive over finite sums. -/
lemma Osc_sum (m n : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ZMod (3 ^ n) → ℝ) :
    Osc m n (fun Y => ∑ i ∈ s, c i Y) ≤ ∑ i ∈ s, Osc m n (c i) := by
  induction s using Finset.induction_on with
  | empty => simp [Osc]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact le_trans (Osc_add m n (c a) _) (add_le_add le_rfl ih)

/-- Tao (6.4)-(6.9) in oscillation form: pieces plus twice the exceptional mass. -/
theorem osc_mu_split (n K m : ℕ) (hmn : m ≤ n) (C L : ℝ) (T D : ℕ) :
    Osc m n (mu n K) ≤ ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc T (T + D),
        Osc m n (dE n K k l (Qs C L T D k)) +
      2 * ∑ w ∈ (Box n K).filter (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w)),
        ((1 : ℝ) / 2) ^ (∑ i, w i) := by
  have hfun : mu n K = fun Y => (fun Y => ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc T (T + D),
      dE n K k l (Qs C L T D k) Y) Y + (fun Y => ∑ w ∈ ((Box n K).filter
        (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w))).filter
        (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)) Y := by
    funext Y; exact mu_decomp n K C L T D Y
  rw [hfun]
  refine le_trans (Osc_add m n _ _) (add_le_add ?_ ?_)
  · refine le_trans (Osc_sum m n (Finset.Icc 1 n) _) (Finset.sum_le_sum (fun k _ => ?_))
    exact Osc_sum m n (Finset.Ioc T (T + D)) _
  · refine le_trans (Osc_le_l1 n m hmn _) ?_
    have hab : ∀ Y : ZMod (3 ^ n), |∑ w ∈ ((Box n K).filter
        (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w))).filter
        (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)| =
        ∑ w ∈ ((Box n K).filter
        (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w))).filter
        (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i) :=
      fun Y => abs_of_nonneg (by positivity)
    simp only [hab]
    rw [Finset.sum_fiberwise]

end Dec7g

/-! ## S11: 7g exceptional mass (Tao (6.3) + single-coordinate tails) -/
section Bad7g
open Finset
open Classical

/-- One coordinate exceeding `D` has mass at most `3 (2/3)^D`. -/
lemma coord_tail (n K D : ℕ) (j0 : Fin n) :
    ∑ w ∈ (Box n K).filter (fun w => D < w j0), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      3 * ((2 : ℝ) / 3) ^ D := by
  set f : Fin n → ℕ → ℝ := fun i v =>
    if i = j0 then (if D < v then ((1 : ℝ) / 2) ^ v else 0) else ((1 : ℝ) / 2) ^ v with hf
  have h1 : ∑ w ∈ (Box n K).filter (fun w => D < w j0), ((1 : ℝ) / 2) ^ (∑ i, w i) =
      ∑ w ∈ Box n K, ∏ i, f i (w i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    by_cases hD : D < w j0
    · rw [if_pos hD]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i = j0
      · subst hi; simp [hf, hD]
      · simp [hf, hi]
    · rw [if_neg hD]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hf, hD])
  rw [h1, Box, ← Finset.prod_univ_sum]
  have hA : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∑ v ∈ Finset.Icc 1 K, f i v := fun i _ =>
    Finset.sum_nonneg (fun v _ => by simp only [hf]; split_ifs <;> positivity)
  have hB : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∑ v ∈ Finset.Icc 1 K, f i v ≤
      if i = j0 then 3 * ((2 : ℝ) / 3) ^ D else 1 := by
    intro i _
    by_cases hi : i = j0
    · rw [if_pos hi]
      have e : ∀ v ∈ Finset.Icc 1 K, f i v ≤ ((2 : ℝ) / 3) ^ D * ((3 : ℝ) / 4) ^ v := by
        intro v _
        simp only [hf, if_pos hi]
        split_ifs with hv
        · have e2 : ((1 : ℝ) / 2) ^ v = ((2 : ℝ) / 3) ^ v * ((3 : ℝ) / 4) ^ v := by
            rw [← mul_pow]; norm_num
          rw [e2]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hv.le) (by positivity)
        · positivity
      refine le_trans (Finset.sum_le_sum e) ?_
      rw [← Finset.mul_sum]
      have hg := geom_Icc_le ((3 : ℝ) / 4) (by norm_num) (by norm_num) K
      have e3 : (3 : ℝ) / 4 / (1 - 3 / 4) = 3 := by norm_num
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) / 3) ^ D := by positivity
      rw [e3] at hg
      (first | linarith | nlinarith)
    · rw [if_neg hi]
      simp only [hf, if_neg hi]
      have hg := geom_Icc_le ((1 : ℝ) / 2) (by norm_num) (by norm_num) K
      have e3 : (1 : ℝ) / 2 / (1 - 1 / 2) = 1 := by norm_num
      linarith
  refine le_trans (Finset.prod_le_prod hA hB) ?_
  simp

lemma sum_filter_exists_fin_le {α : Type*} (S : Finset α) (n : ℕ) (B : Fin n → α → Prop)
    [∀ j, DecidablePred (B j)] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ S.filter (fun a => ∃ j, B j a), f a ≤ ∑ j, ∑ a ∈ S.filter (B j), f a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun a _ => ?_)
  by_cases h : ∃ j, B j a
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩]
    refine le_trans (le_of_eq (if_pos hj).symm)
      (Finset.single_le_sum (f := fun j => if B j a then f a else 0) (fun i _ => ?_)
        (Finset.mem_univ j))
    split_ifs <;> simp [hf a]
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hf a])

/-- Not stopping implies a deviation, a late stop, or one large step (via `Qs_exists`). -/
lemma nostop_sub (n K : ℕ) (C L : ℝ) (T D : ℕ) (w : Fin n → ℕ)
    (hw : ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w)) :
    ¬ DevOK C L (padv w) n ∨
      ((DevOK C L (padv w) n ∧ ps (padv w) n ≤ T) ∨ ∃ j0 : Fin n, D < w j0) := by
  by_contra hcon
  apply hw
  have h1 : DevOK C L (padv w) n := by
    by_contra h; exact hcon (Or.inl h)
  have h2 : T < ps (padv w) n := by
    by_contra h; exact hcon (Or.inr (Or.inl ⟨h1, by omega⟩))
  have h3 : ∀ j0 : Fin n, w j0 ≤ D := fun j0 => by
    by_contra h; exact hcon (Or.inr (Or.inr ⟨j0, by omega⟩))
  refine Qs_exists C L T D n (padv w) h1 h2 (fun j hj => ?_)
  have := h3 ⟨j, hj⟩
  unfold padv; rw [dif_pos hj]; exact this

/-- The three exceptional events, summed. -/
theorem bad3_mass_le (n K : ℕ) (C L : ℝ) (T D : ℕ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n ∨
        ((DevOK C L (padv w) n ∧ ps (padv w) n ≤ T) ∨ ∃ j0 : Fin n, D < w j0)),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      2 * n * Real.exp (-(C * L) / 24) +
      (∑ w ∈ (Box n K).filter (fun w => DevOK C L (padv w) n ∧ ps (padv w) n ≤ T),
        ((1 : ℝ) / 2) ^ (∑ i, w i) + n * (3 * ((2 : ℝ) / 3) ^ D)) := by
  have hf : ∀ w : Fin n → ℕ, (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, w i) := fun _ => by positivity
  have hA := sum_filter_or_le (Box n K) (fun w => ¬ DevOK C L (padv w) n)
    (fun w => (DevOK C L (padv w) n ∧ ps (padv w) n ≤ T) ∨ ∃ j0 : Fin n, D < w j0) _ hf
  have hB := sum_filter_or_le (Box n K) (fun w => DevOK C L (padv w) n ∧ ps (padv w) n ≤ T)
    (fun w => ∃ j0 : Fin n, D < w j0) _ hf
  have hC' := dev_bad_mass n K C L hC hL
  have hD' := sum_filter_exists_fin_le (Box n K) n (fun j0 w => D < w j0) _ hf
  have hE : ∑ j0 : Fin n, ∑ w ∈ (Box n K).filter (fun w => D < w j0), ((1 : ℝ) / 2) ^ (∑ i, w i)
      ≤ n * (3 * ((2 : ℝ) / 3) ^ D) := by
    calc _ ≤ ∑ _j0 : Fin n, 3 * ((2 : ℝ) / 3) ^ D :=
          Finset.sum_le_sum (fun j0 _ => coord_tail n K D j0)
      _ = n * (3 * ((2 : ℝ) / 3) ^ D) := by simp
  linarith

set_option maxHeartbeats 1000000 in
/-- Mass off the stopping-time events: deviations (Tao (6.3)), late stop, or one large step. -/
theorem bad_mass_le (n K : ℕ) (C L : ℝ) (T D : ℕ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    ∑ w ∈ (Box n K).filter (fun w => ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w)),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      2 * n * Real.exp (-(C * L) / 24) +
      (∑ w ∈ (Box n K).filter (fun w => DevOK C L (padv w) n ∧ ps (padv w) n ≤ T),
        ((1 : ℝ) / 2) ^ (∑ i, w i) + n * (3 * ((2 : ℝ) / 3) ^ D)) := by
  refine le_trans ?_ (bad3_mass_le n K C L T D hC hL)
  simp only [Finset.sum_filter]
  refine Finset.sum_le_sum (fun w _ => ?_)
  by_cases h : ¬ ∃ k ∈ Finset.Icc 1 n, Qs C L T D k (padv w)
  · rw [if_pos h, if_pos (nostop_sub n K C L T D w h)]
  · rw [if_neg h]; split_ifs <;> positivity

end Bad7g

/-! ## S12: 7g core bound with explicit parameters (Tao (6.10)-(6.11) summed, plus (6.3)) -/
section Core7g
open Finset
open Classical

lemma Osc_zero (m n : ℕ) : Osc m n (fun _ => 0) = 0 := by
  unfold Osc; simp

lemma dE_eq_zero (n K k l : ℕ) (Q : (ℕ → ℕ) → Prop) (hQ : ∀ w : Fin n → ℕ, ¬ Q (padv w)) :
    dE n K k l Q = fun _ => 0 := by
  funext Y
  unfold dE
  apply Finset.sum_eq_zero
  intro w hw
  simp only [Finset.mem_filter] at hw
  exact absurd hw.1.2.1 (hQ w)

lemma Qs_k_le (C L : ℝ) (T D k n m : ℕ) (a : ℕ → ℕ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 10 * ((T : ℝ) + C * (Real.sqrt (n * L) + L) + 2) ≤ 20 * (m : ℝ) - n)
    (hQ : Qs C L T D k a) : 20 * k + n ≤ 20 * m := by
  obtain ⟨hdev, hT1, -, -⟩ := hQ
  have hs : 0 ≤ Real.sqrt (n * L) := Real.sqrt_nonneg _
  have hTn : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have key : 2 * ((k : ℝ) - 1) ≤ T + C * (Real.sqrt (n * L) + L) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk' : k = 1 := by omega
      subst hk'
      have : 0 ≤ C * (Real.sqrt (n * L) + L) := by positivity
      simp only [Nat.cast_one, sub_self, mul_zero]; linarith
    · have hj := hdev (k - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at hj
      have hle := (abs_le.mp hj).1
      have hps : (ps a (k - 1) : ℝ) ≤ T := by exact_mod_cast hT1
      have hsq : Real.sqrt (((k : ℝ) - 1) * L) ≤ Real.sqrt (n * L) := by
        apply Real.sqrt_le_sqrt
        have hkr : (k : ℝ) ≤ n := by exact_mod_cast hkn
        exact mul_le_mul_of_nonneg_right (by linarith) hL
      have hCs := mul_le_mul_of_nonneg_left hsq hC
      rw [mul_add] at hle ⊢
      linarith
  have : 20 * (k : ℝ) + n ≤ 20 * m := by linarith
  exact_mod_cast this

theorem osc_piece_le (m n K : ℕ) (C L : ℝ) (hC : 10 ≤ C) (hL : 1 ≤ L) (T D : ℕ) (β : ℝ)
    (hβ0 : 0 ≤ β)
    (h1 : (2 : ℝ) ^ (T + D) * (2 : ℝ) ^ ((99 / 100) * C ^ 2 * L) ≤ 3 ^ n)
    (h3 : 10 * ((T : ℝ) + C * (Real.sqrt (n * L) + L) + 2) ≤ 20 * (m : ℝ) - n)
    (hmn : m ≤ n)
    (hB : ∀ r : ℕ, n < 20 * r → r ≤ n → ∀ η : ℤ, ¬ (3 : ℤ) ∣ η → ‖chi r K η‖ ≤ β)
    (k l : ℕ) (hk : k ∈ Finset.Icc 1 n) (hl : l ∈ Finset.Ioc T (T + D)) :
    Osc m n (dE n K k l (Qs C L T D k)) ≤
      β * Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1)) := by
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hbd : 0 ≤ β * Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1)) := by positivity
  by_cases hkm : 20 * k + n ≤ 20 * m
  · refine le_trans (osc_dE_le n k K l m (Qs C L T D k) (fun a b h => Qs_congr C L T D k a b h)
      (by omega) hmn β hβ0 ?_ ?_) ?_
    · intro r hr1 hr2 η hη
      exact hB r (by omega) (by omega) η hη
    · intro u _ hQ
      apply Fnat_lt_of_dev (padv u) k n C L hC hL
      · refine le_trans ?_ h1
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hQ.2.2.2
      · intro j hj
        have h := hQ.1 (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        push_cast at h
        have h2 := (abs_le.mp h).1
        rw [mul_add] at h2
        linarith
    · apply mul_le_mul_of_nonneg_left _ hβ0
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  · have hz : dE n K k l (Qs C L T D k) = fun _ => 0 := by
      apply dE_eq_zero
      intro w hQ
      exact hkm (Qs_k_le C L T D k n m (padv w) (by linarith) (by linarith) hk.1 hk.2 h3 hQ)
    rw [hz, Osc_zero]; exact hbd

/-- Tao (6.2)-(6.11) with explicit parameters: the whole oscillation bound for one `(m, n)`. -/
theorem osc_core (m n K : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (C L : ℝ) (hC : 10 ≤ C) (hL : 1 ≤ L)
    (T D : ℕ) (β : ℝ) (hβ0 : 0 ≤ β)
    (h1 : (2 : ℝ) ^ (T + D) * (2 : ℝ) ^ ((99 / 100) * C ^ 2 * L) ≤ 3 ^ n)
    (h2 : (T : ℝ) + C * (Real.sqrt (n * L) + L) < 2 * n)
    (h3 : 10 * ((T : ℝ) + C * (Real.sqrt (n * L) + L) + 2) ≤ 20 * (m : ℝ) - n)
    (hB : ∀ r : ℕ, n < 20 * r → r ≤ n → ∀ η : ℤ, ¬ (3 : ℤ) ∣ η → ‖chi r K η‖ ≤ β) :
    Osc m n (mu n K) ≤ n * D * (β * Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1))) +
      2 * (2 * n * Real.exp (-(C * L) / 24) + n * (3 * ((2 : ℝ) / 3) ^ D)) := by
  refine le_trans (osc_mu_split n K m hmn C L T D) ?_
  have hsum : ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc T (T + D),
      Osc m n (dE n K k l (Qs C L T D k)) ≤
      n * D * (β * Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1))) := by
    have := Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl =>
      osc_piece_le m n K C L hC hL T D β hβ0 h1 h3 hmn hB k l hk hl))
    refine le_trans this (le_of_eq ?_)
    simp only [Finset.sum_const, Nat.card_Icc, Nat.card_Ioc, nsmul_eq_mul, Nat.add_sub_cancel,
      Nat.add_sub_cancel_left]
    ring
  have hmid : ∑ w ∈ (Box n K).filter (fun w => DevOK C L (padv w) n ∧ ps (padv w) n ≤ T),
      ((1 : ℝ) / 2) ^ (∑ i, w i) = 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    rintro ⟨hd, hp⟩
    have h := hd n (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have h' := (abs_le.mp h).1
    have hp' : (ps (padv w) n : ℝ) ≤ T := by exact_mod_cast hp
    linarith
  have hbad := bad_mass_le n K C L T D (by linarith) (by linarith)
  rw [hmid, zero_add] at hbad
  linarith

end Core7g

/-! ## S12b: asymptotic bookkeeping, `Prop117 → Prop114w` (Tao (6.2), end of Section 6) -/
section Fin7g

lemma log3_le : Real.log 3 * 5 ≤ Real.log 2 * 8 := by
  have h1 : Real.log ((3 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 8) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h1
  push_cast at h1
  linarith

lemma log_le_two_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

lemma large_log (C x : ℝ) (hx0 : 0 < x) (hx : (800 * C ^ 2) ^ 2 ≤ x) :
    400 * C ^ 2 * Real.log x ≤ x := by
  have hC0 : 0 ≤ 800 * C ^ 2 := by positivity
  have hs : 800 * C ^ 2 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_sq hC0] at h
  have hl := log_le_two_sqrt x hx0
  have hsx := Real.mul_self_sqrt hx0.le
  have e1 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 400 * C ^ 2)
  have e2 := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
  (first | linarith | nlinarith)

set_option maxHeartbeats 1000000 in
theorem osc_large (A C A' C2 lam L : ℝ) (hA : 0 < A) (hC : C = 24 * (A + 3) + 10)
    (hA' : A' = A + 2 + C ^ 2) (hC2p : 0 < C2)
    (hC2 : ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
      ‖chi n K ξ‖ ≤ C2 * (n : ℝ) ^ (-A'))
    (hlam : lam * Real.log 2 = Real.log 3)
    (m n K : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (h9 : 9 * n ≤ 10 * m) (hnK : n ≤ K)
    (hn40 : 40 ≤ n) (hnC : (800 * C ^ 2) ^ 2 ≤ (n : ℝ)) (hL : L = Real.log n) :
    Osc m n (mu n K) ≤ (C ^ 2 * C2 * Real.exp (A' * Real.log 20) + 22) * Real.exp (-A * L) := by
  have hx40 : (40 : ℝ) ≤ n := by exact_mod_cast hn40
  have hx0 : (0 : ℝ) < n := by linarith
  have hC10 : 10 ≤ C := by rw [hC]; linarith
  have hA'0 : 0 < A' := by rw [hA']; positivity
  have hL1 : 1 ≤ L := by
    have he : Real.exp 1 ≤ n := by have := Real.exp_one_lt_d9; linarith
    rw [hL]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) he
  have hL0 : 0 ≤ L := by linarith
  have hlarge : 400 * C ^ 2 * L ≤ n := by rw [hL]; exact large_log C n hx0 hnC
  have hC2L : 0 ≤ C ^ 2 * L := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlam1 : 1 ≤ lam := by
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    by_contra hc
    push_neg at hc
    have := mul_lt_mul_of_pos_right hc hlog2
    linarith
  have hlam2 : lam ≤ 8 / 5 := by
    have := log3_le
    by_contra hc
    push_neg at hc
    have := mul_lt_mul_of_pos_right hc hlog2
    linarith
  have hCp : 0 < C := by linarith
  have hsq : C * Real.sqrt (n * L) ≤ n / 20 := by
    have h1 : (n : ℝ) * L ≤ (n / (20 * C)) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have e := mul_le_mul_of_nonneg_left hlarge hx0.le
      linarith
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (by positivity)] at h2
    calc C * Real.sqrt (n * L) ≤ C * (n / (20 * C)) := mul_le_mul_of_nonneg_left h2 hCp.le
      _ = n / 20 := by field_simp <;> ring
  have hnl1 := mul_le_mul_of_nonneg_left hlam1 hx0.le
  have hTarg : 0 ≤ (n : ℝ) * lam - C ^ 2 * L := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ⌊(n : ℝ) * lam - C ^ 2 * L⌋₊ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = ⌊C ^ 2 * L / 100⌋₊ := ⟨_, rfl⟩
  have hT1 : (T : ℝ) ≤ n * lam - C ^ 2 * L := by rw [hTdef]; exact Nat.floor_le hTarg
  have hT2 : (n : ℝ) * lam - C ^ 2 * L < T + 1 := by rw [hTdef]; exact Nat.lt_floor_add_one _
  have hD1 : (D : ℝ) ≤ C ^ 2 * L / 100 := by rw [hDdef]; exact Nat.floor_le (by positivity)
  have hD2 : C ^ 2 * L / 100 < D + 1 := by rw [hDdef]; exact Nat.lt_floor_add_one _
  have hnlam : (n : ℝ) * lam * Real.log 2 = n * Real.log 3 := by rw [mul_assoc, hlam]
  have e3 : (3 : ℝ) ^ n = Real.exp (n * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h1 : (2 : ℝ) ^ (T + D) * (2 : ℝ) ^ ((99 / 100) * C ^ 2 * L) ≤ 3 ^ n := by
    rw [← Real.rpow_natCast (2 : ℝ) (T + D), Real.rpow_def_of_pos two_pos,
      Real.rpow_def_of_pos two_pos, ← Real.exp_add, e3]
    apply Real.exp_le_exp.mpr
    have hs : ((T + D : ℕ) : ℝ) + (99 / 100) * C ^ 2 * L ≤ n * lam := by push_cast; linarith
    have := mul_le_mul_of_nonneg_left hs hlog2.le
    linarith
  have hCL : C * L ≤ C ^ 2 * L := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - 1) (mul_nonneg hCp.le hL0)]
  have hnl : (n : ℝ) * lam ≤ n * (8 / 5) := mul_le_mul_of_nonneg_left hlam2 hx0.le
  have h2 : (T : ℝ) + C * (Real.sqrt (n * L) + L) < 2 * n := by
    rw [mul_add C]; linarith
  have hm9 : 9 * (n : ℝ) ≤ 10 * m := by exact_mod_cast h9
  have h3 : 10 * ((T : ℝ) + C * (Real.sqrt (n * L) + L) + 2) ≤ 20 * (m : ℝ) - n := by
    rw [mul_add C]; linarith
  have hB : ∀ r : ℕ, n < 20 * r → r ≤ n → ∀ η : ℤ, ¬ (3 : ℤ) ∣ η →
      ‖chi r K η‖ ≤ C2 * Real.exp (A' * Real.log 20) * Real.exp (-A' * L) := by
    intro r hr1 hr2 η hη
    have hr0 : (0 : ℝ) < r := by
      have : 1 ≤ r := by omega
      exact_mod_cast this
    refine le_trans (hC2 r K (by omega) (le_trans hr2 hnK) η hη) ?_
    rw [Real.rpow_def_of_pos hr0, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC2p.le
    apply Real.exp_le_exp.mpr
    have hlr : L ≤ Real.log 20 + Real.log r := by
      rw [← Real.log_mul (by norm_num) hr0.ne', hL]
      apply Real.log_le_log hx0
      exact_mod_cast hr1.le
    linarith [mul_le_mul_of_nonneg_left hlr hA'0.le]
  have hS : Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1)) ≤ Real.exp (C ^ 2 * L) := by
    have e2 : ((1 : ℝ) / 2) ^ (T + 1) = Real.exp (((T + 1 : ℕ) : ℝ) * (-Real.log 2)) := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hY : (3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1) ≤ Real.exp (C ^ 2 * L) ^ 2 := by
      rw [e3, e2, ← Real.exp_add, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have := mul_lt_mul_of_pos_right hT2 hlog2
      have h22 := mul_le_mul_of_nonneg_left hlog2'.le hC2L
      push_cast
      linarith
    have h := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_sq (by positivity)] at h
  have hcore := osc_core m n K hm hmn C L hC10 hL1 T D
    (C2 * Real.exp (A' * Real.log 20) * Real.exp (-A' * L)) (by positivity) h1 h2 h3 hB
  have hn : (n : ℝ) = Real.exp L := by rw [hL, Real.exp_log hx0]
  have hD' : (D : ℝ) ≤ C ^ 2 * Real.exp L := by
    have := Real.add_one_le_exp L
    linarith [mul_le_mul_of_nonneg_left this (sq_nonneg C), sq_nonneg C]
  have hmain : (n : ℝ) * D * (C2 * Real.exp (A' * Real.log 20) * Real.exp (-A' * L) *
      Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1))) ≤
      C ^ 2 * C2 * Real.exp (A' * Real.log 20) * Real.exp (-A * L) := by
    have hβ0 : 0 ≤ C2 * Real.exp (A' * Real.log 20) * Real.exp (-A' * L) := by positivity
    calc (n : ℝ) * D * (C2 * Real.exp (A' * Real.log 20) * Real.exp (-A' * L) *
          Real.sqrt ((3 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (T + 1)))
        ≤ Real.exp L * (C ^ 2 * Real.exp L) * (C2 * Real.exp (A' * Real.log 20) *
          Real.exp (-A' * L) * Real.exp (C ^ 2 * L)) := by
          apply mul_le_mul (mul_le_mul hn.le hD' (Nat.cast_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_left hS hβ0) (by positivity) (by positivity)
      _ = C ^ 2 * C2 * Real.exp (A' * Real.log 20) * Real.exp (-A * L) := by
          have hE : Real.exp L * Real.exp L * Real.exp (-A' * L) * Real.exp (C ^ 2 * L) =
              Real.exp (-A * L) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hA']; congr 1; ring
          linear_combination (C ^ 2 * C2 * Real.exp (A' * Real.log 20)) * hE
  have hbad1 : 2 * (n : ℝ) * Real.exp (-(C * L) / 24) ≤ 2 * Real.exp (-A * L) := by
    rw [hn, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [hC]; linarith
  have hbad2 : (n : ℝ) * (3 * ((2 : ℝ) / 3) ^ D) ≤ 9 * Real.exp (-A * L) := by
    have hq : (2 : ℝ) / 3 ≤ Real.exp (-1 / 3) := by
      have := Real.add_one_le_exp (-1 / 3 : ℝ); linarith
    have hpow : ((2 : ℝ) / 3) ^ D ≤ Real.exp ((D : ℝ) * (-1 / 3)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) hq D
    have he13 : Real.exp (1 / 3) ≤ 3 := by
      have h1 : Real.exp (1 / 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      have := Real.exp_one_lt_d9; linarith
    have hCC : 300 * (1 + A) ≤ C ^ 2 := by rw [hC]; (first | linarith [sq_nonneg A] | nlinarith [sq_nonneg A])
    have hCCL := mul_le_mul_of_nonneg_right hCC hL0
    have hexp : Real.exp L * Real.exp ((D : ℝ) * (-1 / 3)) ≤
        Real.exp (1 / 3) * Real.exp (-A * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc (n : ℝ) * (3 * ((2 : ℝ) / 3) ^ D) = 3 * ((n : ℝ) * ((2 : ℝ) / 3) ^ D) := by ring
      _ ≤ 3 * (Real.exp L * Real.exp ((D : ℝ) * (-1 / 3))) := by
          rw [← hn]; gcongr
      _ ≤ 3 * (Real.exp (1 / 3) * Real.exp (-A * L)) := by gcongr
      _ ≤ 3 * (3 * Real.exp (-A * L)) := by gcongr
      _ = 9 * Real.exp (-A * L) := by ring
  linarith

/-- Tao (6.2): Proposition 1.17 implies the weak form of Proposition 1.14. -/
theorem prop114w_of_117 (h117 : Prop117) : Prop114w := by
  intro A hA
  obtain ⟨C2, hC2p, hC2⟩ := h117 (A + 2 + (24 * (A + 3) + 10) ^ 2) (by positivity)
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ⌈(800 * (24 * (A + 3) + 10) ^ 2) ^ 2⌉₊ + 40 := ⟨_, rfl⟩
  have hlam : Real.log 3 / Real.log 2 * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne'
  refine ⟨((24 * (A + 3) + 10) ^ 2 * C2 *
      Real.exp ((A + 2 + (24 * (A + 3) + 10) ^ 2) * Real.log 20) + 22) +
      2 * Real.exp (A * Real.log N0), by positivity, ?_⟩
  intro m n K hm hmn h9 hnK
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogm : Real.log m ≤ Real.log n := Real.log_le_log hmpos (by exact_mod_cast hmn)
  rw [Real.rpow_def_of_pos hmpos]
  have hK1 : 0 ≤ (24 * (A + 3) + 10) ^ 2 * C2 *
      Real.exp ((A + 2 + (24 * (A + 3) + 10) ^ 2) * Real.log 20) + 22 := by positivity
  have hEm : 0 ≤ Real.exp (Real.log m * -A) := (Real.exp_pos _).le
  have hE2 : 0 ≤ 2 * Real.exp (A * Real.log N0) := by positivity
  by_cases hN : N0 ≤ n
  · have hn40 : 40 ≤ n := by omega
    have hnC : (800 * (24 * (A + 3) + 10) ^ 2) ^ 2 ≤ (n : ℝ) := by
      have h1 := Nat.le_ceil ((800 * (24 * (A + 3) + 10) ^ 2) ^ 2)
      have h2 : ((⌈(800 * (24 * (A + 3) + 10) ^ 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (show ⌈(800 * (24 * (A + 3) + 10) ^ 2) ^ 2⌉₊ ≤ n by omega)
      linarith
    have hb := osc_large A (24 * (A + 3) + 10) (A + 2 + (24 * (A + 3) + 10) ^ 2) C2
      (Real.log 3 / Real.log 2) (Real.log n) hA rfl rfl hC2p hC2 hlam m n K hm hmn h9 hnK
      hn40 hnC rfl
    refine le_trans hb ?_
    have hexp : Real.exp (-A * Real.log n) ≤ Real.exp (Real.log m * -A) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlogm hA.le])
    (first | linarith [mul_le_mul_of_nonneg_left hexp hK1, mul_nonneg hE2 hEm] | nlinarith [mul_le_mul_of_nonneg_left hexp hK1, mul_nonneg hE2 hEm])
  · have h2 := Osc_mu_le_two m n K hmn
    have hlogN : Real.log m ≤ Real.log N0 :=
      Real.log_le_log hmpos (by exact_mod_cast (show m ≤ N0 by omega))
    have h1 : 1 ≤ Real.exp (A * Real.log N0) * Real.exp (Real.log m * -A) := by
      rw [← Real.exp_add]
      have := Real.add_one_le_exp (A * Real.log N0 + Real.log m * -A)
      (first | linarith [mul_nonneg hA.le (sub_nonneg.mpr hlogN)] | nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hlogN)])
    (first | linarith [mul_nonneg hK1 hEm] | nlinarith [mul_nonneg hK1 hEm])

/-- Tao Section 6 in full: Proposition 1.17 implies Proposition 1.14. -/
theorem prop114_of_117 (h117 : Prop117) : Prop114 := prop114_of_weak (prop114w_of_117 h117)

end Fin7g

/-- Def-free form of Prop 1.17 (child statement body). -/
def Prop117_inl : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ C * (n : ℝ) ^ (-A)

theorem prop117_iff : Prop117 ↔ Prop117_inl := by
  simp only [Prop117, Prop117_inl, chi, syrZ, Fnat, ps_eq_sum, padv, Box]


/-- Def-free `mu` equation (child statement form). -/
def MuEq (n K : ℕ) (μ : ZMod (3 ^ n) → ℝ) : Prop :=
  ∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)

theorem mu_MuEq (n K : ℕ) : MuEq n K (mu n K) := by
  intro Y
  unfold mu Box syrZ Fnat padv
  simp only [ps_eq_sum]
  all_goals first
    | rfl
    | (congr 1; ext w; simp)
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

theorem Osc_eq_inl (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : Osc m n c =
    ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'| := by
  unfold Osc
  first
    | rfl
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

/-- Def-free Prop 1.14 (child statement body, `MuEq` unfolded in the spec). -/
def Prop114_inl : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, MuEq n K μ →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A)

theorem prop114_iff : Prop114 ↔ Prop114_inl := by
  constructor
  · intro h A hA
    obtain ⟨C, hC, hb⟩ := h A hA
    refine ⟨C, hC, fun m n K h1 h2 h3 μ hμ => ?_⟩
    have hμ' : μ = mu n K := funext fun Y => (hμ Y).trans (mu_MuEq n K Y).symm
    subst hμ'
    rw [← Osc_eq_inl]; exact hb m n K h1 h2 h3
  · intro h A hA
    obtain ⟨C, hC, hb⟩ := h A hA
    exact ⟨C, hC, fun m n K h1 h2 h3 => by
      rw [Osc_eq_inl]; exact hb m n K h1 h2 h3 _ (mu_MuEq n K)⟩


end Tao31

open Tao31 in
theorem solution :
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ C * (n : ℝ) ^ (-A)) →
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, (∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)) →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A) := by
  intro h
  exact Tao31.prop114_iff.1 (Tao31.prop114_of_117 (Tao31.prop117_iff.2 h))
