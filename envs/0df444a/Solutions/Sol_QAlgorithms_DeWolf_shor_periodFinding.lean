-- Prove2me | solution 1 for QAlgorithms.DeWolf.shor_periodFinding
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-19T20:02:44.875304+00:00
-- url     : https://prove2.me/submissions/c3e43005-273e-497e-8dab-dca98d1c5150

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace ShorNT

open Real Finset

/-- primes `≤ n` -/
def P (n : ℕ) : Finset ℕ := (range (n + 1)).filter Nat.Prime

lemma mem_P {n p : ℕ} : p ∈ P n ↔ p ≤ n ∧ p.Prime := by
  simp [P, Nat.lt_succ_iff]

lemma P_succ (n : ℕ) : P (n + 1) = if (n + 1).Prime then insert (n + 1) (P n) else P n := by
  unfold P; rw [range_add_one (n := n + 1), filter_insert]

noncomputable def A (n : ℕ) : ℝ := ∑ p ∈ P n, Real.log p / p

lemma theta_P (n : ℕ) : ∑ p ∈ P n, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h

lemma sum_log_mul_div_le (n : ℕ) :
    ∑ p ∈ P n, Real.log p * ((n / p : ℕ) : ℝ) ≤ n * Real.log n := by
  have h1 : ∀ m ∈ range n,
      ∑ p ∈ P n, (if p ∣ m + 1 then Real.log p else 0) ≤ Real.log ((m : ℝ) + 1) := by
    intro m hm
    rw [mem_range] at hm
    rw [← Finset.sum_filter]
    have hset : (P n).filter (fun p => p ∣ m + 1) = (m + 1).primeFactors := by
      ext p
      simp only [mem_filter, mem_P, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨_, hp⟩, hd⟩; exact ⟨hp, hd, by omega⟩
      · rintro ⟨hp, hd, _⟩
        have := Nat.le_of_dvd (by omega) hd
        exact ⟨⟨by omega, hp⟩, hd⟩
    rw [hset, ← Real.log_prod (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity), ← Nat.cast_prod]
    apply Real.log_le_log
    · apply Nat.cast_pos.2
      exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    · have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd (m + 1))
      exact_mod_cast this
  calc ∑ p ∈ P n, Real.log p * ((n / p : ℕ) : ℝ)
      = ∑ p ∈ P n, ∑ m ∈ range n, (if p ∣ m + 1 then Real.log p else 0) := by
        apply sum_congr rfl; intro p _
        rw [← Finset.sum_filter, sum_const, ← Nat.card_multiples n p, nsmul_eq_mul, mul_comm]
    _ = ∑ m ∈ range n, ∑ p ∈ P n, (if p ∣ m + 1 then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ m ∈ range n, Real.log ((m : ℝ) + 1) := sum_le_sum h1
    _ ≤ ∑ m ∈ range n, Real.log n := by
        apply sum_le_sum; intro m hm; rw [mem_range] at hm
        apply Real.log_le_log (by positivity)
        have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
        push_cast at this; exact this
    _ = n * Real.log n := by simp

/-- Mertens' first theorem, upper half. -/
lemma A_le (n : ℕ) (hn : 1 ≤ n) : A n ≤ Real.log n + Real.log 4 := by
  have h1 := sum_log_mul_div_le n
  have h2 := theta_P n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : ∀ p ∈ P n, Real.log p * ((n : ℝ) / p - 1) ≤ Real.log p * ((n / p : ℕ) : ℝ) := by
    intro p hp
    have hpp := (mem_P.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
    have := Nat.lt_div_mul_add (a := n) hpp.pos
    have : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast this
    linarith
  have h4 : ∑ p ∈ P n, Real.log p * ((n : ℝ) / p - 1) = n * A n - ∑ p ∈ P n, Real.log p := by
    rw [A, mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro p _; ring
  have h5 := sum_le_sum h3
  rw [h4] at h5
  have : n * A n ≤ n * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left this hn'

noncomputable def S (n : ℕ) : ℝ := ∑ p ∈ P n, 1 / ((p : ℝ) - 1)

noncomputable def U (n : ℕ) : ℝ :=
  S n - A n / Real.log n - Real.log (Real.log n) + Real.log 4 / Real.log n + 1 / n

lemma U_succ_le (n : ℕ) (hn : 2 ≤ n) : U (n + 1) ≤ U n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 < Real.log n := Real.log_pos (by linarith)
  have hL01 : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by positivity) (by linarith)
  have hL1 : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le hL0 hL01
  have hA := A_le n (by omega)
  have hΔ : 1 - Real.log n / Real.log ((n : ℝ) + 1) ≤
      Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
    have := Real.log_le_sub_one_of_pos (div_pos hL0 hL1)
    rw [Real.log_div hL0.ne' hL1.ne'] at this; linarith
  have h0 : 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hL0 hL01
  have hkey : A n / Real.log n - A n / Real.log ((n : ℝ) + 1) - Real.log 4 / Real.log n +
      Real.log 4 / Real.log ((n : ℝ) + 1) ≤ 1 - Real.log n / Real.log ((n : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_right (show A n - Real.log 4 ≤ Real.log n by linarith) h0
    have e1 : (A n - Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
        A n / Real.log n - A n / Real.log ((n : ℝ) + 1) - Real.log 4 / Real.log n +
        Real.log 4 / Real.log ((n : ℝ) + 1) := by ring
    have e2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
        1 - Real.log n / Real.log ((n : ℝ) + 1) := by field_simp
    linarith
  have hn0 : (0 : ℝ) < n := by positivity
  have hrec : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hn0 (by linarith)
  have hnot : n + 1 ∉ P n := by simp [mem_P]
  unfold U S A
  rw [P_succ]
  push_cast
  split_ifs with hp
  · rw [sum_insert hnot, sum_insert hnot]
    simp only [Nat.cast_add, Nat.cast_one]
    have e3 : (1 : ℝ) / ((n : ℝ) + 1 - 1) = 1 / n := by ring_nf
    have e4 : (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) + ∑ p ∈ P n, Real.log p / p) /
        Real.log ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) +
          (∑ p ∈ P n, Real.log p / p) / Real.log ((n : ℝ) + 1) := by
      field_simp
    rw [e3, e4]
    unfold A at hkey
    linarith
  · unfold A at hkey
    linarith

lemma U_le (n : ℕ) (hn : 2 ≤ n) : U n ≤ U 2 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (U_succ_le k hk).trans ih

lemma S_le (n : ℕ) (hn : 2 ≤ n) : S n ≤ Real.log (Real.log n) + (U 2 + 1) := by
  have h := U_le n hn
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hA := A_le n (by omega)
  have h1 : A n / Real.log n ≤ 1 + Real.log 4 / Real.log n := by
    rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']; linarith
  have h2 : (0 : ℝ) ≤ 1 / n := by positivity
  have hU : U n = S n - A n / Real.log n - Real.log (Real.log n) + Real.log 4 / Real.log n +
    1 / n := rfl
  linarith

lemma log_ratio_le (r : ℕ) (hr : 1 ≤ r) :
    Real.log ((r : ℝ) / Nat.totient r) ≤ ∑ p ∈ r.primeFactors, 1 / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors r
  have hpos : ∀ p ∈ r.primeFactors, (1 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hcast : (Nat.totient r : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ) =
      r * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]; congr 1; apply prod_congr rfl; intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]; simp
  have hratio : (r : ℝ) / Nat.totient r = ∏ p ∈ r.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [prod_div_distrib]
    have hne : ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) ≠ 0 :=
      prod_ne_zero_iff.2 (fun p hp => by linarith [hpos p hp])
    rw [div_eq_div_iff hφ.ne' hne]
    linear_combination (-1 : ℝ) * hcast
  rw [hratio, Real.log_prod (fun p hp => by
    have := hpos p hp; exact (div_pos (by linarith) (by linarith)).ne')]
  apply sum_le_sum; intro p hp
  have := hpos p hp
  calc Real.log ((p : ℝ) / (p - 1)) ≤ (p : ℝ) / (p - 1) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
    _ = 1 / ((p : ℝ) - 1) := by
      have hp1 : (p : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < p - 1).ne'
      field_simp; ring

lemma sum_large (r y : ℕ) (hr : 1 ≤ r) (hy : 1 ≤ y) :
    ∑ p ∈ r.primeFactors.filter (fun p => y < p), 1 / ((p : ℝ) - 1) ≤
      Real.log r / (y * Real.log ((y : ℝ) + 1)) := by
  set Q := r.primeFactors.filter (fun p => y < p) with hQ
  have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hterm : ∀ p ∈ Q, 1 / ((p : ℝ) - 1) ≤ 1 / y := by
    intro p hp
    rw [hQ, mem_filter] at hp
    have : (y : ℝ) + 1 ≤ p := by exact_mod_cast hp.2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hcard : (Q.card : ℝ) * Real.log ((y : ℝ) + 1) ≤ Real.log r := by
    have h1 : (y + 1) ^ Q.card ≤ ∏ p ∈ Q, p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => by rw [hQ, mem_filter] at hp; omega)
    have h2 : ∏ p ∈ Q, p ≤ r := by
      have : ∏ p ∈ Q, p ∣ ∏ p ∈ r.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
      exact Nat.le_of_dvd (by omega) (this.trans (Nat.prod_primeFactors_dvd r))
    have h3 : ((y : ℝ) + 1) ^ Q.card ≤ r := by exact_mod_cast h1.trans h2
    have := Real.log_le_log (by positivity) h3
    rwa [Real.log_pow] at this
  have hl : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  calc ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ≤ ∑ p ∈ Q, 1 / (y : ℝ) := sum_le_sum hterm
    _ = Q.card / y := by simp [div_eq_mul_inv]
    _ ≤ Real.log r / (y * Real.log ((y : ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ y)
      nlinarith

lemma sum_small (r y : ℕ) :
    ∑ p ∈ r.primeFactors.filter (fun p => ¬ y < p), 1 / ((p : ℝ) - 1) ≤ S y := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [mem_filter, Nat.mem_primeFactors, not_lt] at hp
    exact mem_P.2 ⟨hp.2, hp.1.1⟩
  · intro p hp _
    have := (mem_P.1 hp).2.one_lt
    have : (1 : ℝ) < p := by exact_mod_cast this
    exact (one_div_pos.2 (by linarith)).le

/-- `φ(r)/r ≥ C / log log N` for `r ≤ N`. -/
theorem totient_lower : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 256 ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
    C / Real.log (Real.log N) ≤ (Nat.totient r : ℝ) / r := by
  set K := U 2 + 1
  refine ⟨Real.exp (-(K + 2)), Real.exp_pos _, fun N hN r hr hrN => ?_⟩
  have hN' : (256 : ℝ) ≤ N := by exact_mod_cast hN
  set LN := Real.log N with hLN
  have hLN5 : 5 ≤ LN := by
    have h256 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hN'
    have := Real.log_two_gt_d9
    linarith
  set y := ⌊LN⌋₊ with hy
  have hy5 : 5 ≤ y := Nat.le_floor (by exact_mod_cast hLN5)
  have hyle : (y : ℝ) ≤ LN := Nat.floor_le (by linarith)
  have hylt : LN < (y : ℝ) + 1 := Nat.lt_floor_add_one LN
  have hy5' : (5 : ℝ) ≤ y := by exact_mod_cast hy5
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy1 : 1 ≤ Real.log ((y : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : Real.log r ≤ LN := Real.log_le_log (by linarith) (by exact_mod_cast hrN)
  -- the bound on log(r/φ r)
  have hsplit := sum_filter_add_sum_filter_not r.primeFactors (fun p => y < p)
    (fun p => 1 / ((p : ℝ) - 1))
  have hbig : Real.log r / (y * Real.log ((y : ℝ) + 1)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS := S_le y (by omega)
  have hmain : Real.log ((r : ℝ) / Nat.totient r) ≤ Real.log (Real.log y) + (K + 2) := by
    have := log_ratio_le r hr
    have := sum_large r y hr (by omega)
    have := sum_small r y
    linarith
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hlogLN : 0 < Real.log LN := Real.log_pos (by linarith)
  have hrφ : (r : ℝ) / Nat.totient r ≤ Real.exp (K + 2) * Real.log LN := by
    have h1 := (Real.log_le_iff_le_exp (by positivity)).1 hmain
    rw [Real.exp_add, Real.exp_log hlogy] at h1
    have h2 : Real.log y ≤ Real.log LN := Real.log_le_log (by linarith) hyle
    nlinarith [Real.exp_pos (K + 2)]
  have hr1 : (r : ℝ) ≤ Real.exp (K + 2) * Real.log LN * Nat.totient r := by
    rwa [div_le_iff₀ hφ] at hrφ
  rw [div_le_div_iff₀ hlogLN (by linarith)]
  have he : Real.exp (-(K + 2)) * Real.exp (K + 2) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-(K + 2)) * r ≤ Real.exp (-(K + 2)) * (Real.exp (K + 2) * Real.log LN * Nat.totient r) :=
        mul_le_mul_of_nonneg_left hr1 (Real.exp_pos _).le
    _ = Nat.totient r * Real.log LN := by rw [← mul_assoc, ← mul_assoc, he]; ring

end ShorNT


open Finset

namespace ShorQ
open QAlgorithms

lemma sumSq (m : ℕ) (c : ℝ) : ∑ j ∈ range m, ((j : ℝ) - c) ^ 2 =
    ((m : ℝ) - 1) * m * (2 * m - 1) / 6 - c * m * (m - 1) + m * c ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The geometric-sum lower bound behind Shor's analysis. -/
lemma geo (q r b s c m : ℕ) (hq : 0 < q) (hm : 1 ≤ m) (hmr : (m - 1) * r ≤ q) (hqr : 16 * r ≤ q)
    (hb : |(b : ℝ) * r - c * q| ≤ r / 2) :
    (m : ℝ) / 2 ≤ ‖∑ j ∈ range m, Complex.exp (2 * Real.pi * Complex.I *
      ((b * (s + j * r) : ℕ) : ℂ) / (q : ℂ))‖ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set θ : ℝ := 2 * Real.pi * ((b : ℝ) * r - c * q) / q with hθ
  set φ : ℝ := 2 * Real.pi * b * s / q + ((m : ℝ) - 1) * θ / 2 with hφ
  have hterm : ∀ j ∈ range m, (Complex.exp (-(φ : ℂ) * Complex.I) * Complex.exp (2 * Real.pi *
      Complex.I * ((b * (s + j * r) : ℕ) : ℂ) / (q : ℂ))).re =
      Real.cos (((j : ℝ) - ((m : ℝ) - 1) / 2) * θ + ((j * c : ℕ) : ℝ) * (2 * Real.pi)) := by
    intro j _
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [← Complex.exp_add]
    have : -(φ : ℂ) * Complex.I + 2 * Real.pi * Complex.I * ((b * (s + j * r) : ℕ) : ℂ) / (q : ℂ) =
        ((((j : ℝ) - ((m : ℝ) - 1) / 2) * θ + ((j * c : ℕ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
          Complex.I := by
      rw [hφ, hθ]; push_cast; field_simp; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have hcos : ∀ j ∈ range m, 1 - (((j : ℝ) - ((m : ℝ) - 1) / 2) * θ) ^ 2 / 2 ≤
      Real.cos (((j : ℝ) - ((m : ℝ) - 1) / 2) * θ + ((j * c : ℕ) : ℝ) * (2 * Real.pi)) := by
    intro j _
    rw [Real.cos_add_nat_mul_two_pi]
    exact Real.one_sub_sq_div_two_le_cos
  -- the size of θ
  have hθabs : |θ| ≤ Real.pi * r / q := by
    rw [hθ, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hq', div_le_div_iff_of_pos_right hq']
    nlinarith [Real.pi_pos]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmr' : ((m : ℝ) - 1) * r ≤ q := by
    have := hmr; rw [Nat.sub_mul] at this
    have h2 : ((m * r - 1 * r : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    rw [Nat.cast_sub (Nat.mul_le_mul_right _ hm)] at h2; push_cast at h2; linarith
  have hqr' : 16 * (r : ℝ) ≤ q := by exact_mod_cast hqr
  have hX : |θ| * ((m : ℝ) - 1) ≤ Real.pi := by
    calc |θ| * ((m : ℝ) - 1) ≤ Real.pi * r / q * ((m : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hθabs (by linarith)
      _ = Real.pi * (((m : ℝ) - 1) * r) / q := by ring
      _ ≤ Real.pi * q / q := by gcongr
      _ = Real.pi := by field_simp
  have hY : |θ| * ((m : ℝ) + 1) ≤ Real.pi * (9 / 8) := by
    have h2 : |θ| * 2 ≤ Real.pi / 8 := by
      calc |θ| * 2 ≤ Real.pi * r / q * 2 := by linarith
        _ = Real.pi * (16 * r) / q / 8 := by ring
        _ ≤ Real.pi * q / q / 8 := by gcongr
        _ = Real.pi / 8 := by field_simp
    linarith
  have hθ2 : θ ^ 2 * ((m : ℝ) ^ 2 - 1) ≤ 12 := by
    have e : θ ^ 2 * ((m : ℝ) ^ 2 - 1) = (|θ| * ((m : ℝ) - 1)) * (|θ| * ((m : ℝ) + 1)) := by
      rw [← sq_abs θ]; ring
    have hpi := Real.pi_lt_d2
    have h0 : 0 ≤ |θ| * ((m : ℝ) - 1) := mul_nonneg (abs_nonneg _) (by linarith)
    rw [e]
    calc (|θ| * ((m : ℝ) - 1)) * (|θ| * ((m : ℝ) + 1)) ≤ Real.pi * (Real.pi * (9 / 8)) :=
          mul_le_mul hX hY (mul_nonneg (abs_nonneg _) (by linarith)) Real.pi_pos.le
      _ ≤ 12 := by nlinarith [Real.pi_pos]
  -- assemble
  set T := ∑ j ∈ range m, Complex.exp (2 * Real.pi * Complex.I *
      ((b * (s + j * r) : ℕ) : ℂ) / (q : ℂ))
  have hnorm : ‖T‖ = ‖Complex.exp (-(φ : ℂ) * Complex.I) * T‖ := by
    rw [norm_mul, show -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hnorm]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [mul_sum, Complex.re_sum, sum_congr rfl hterm]
  refine le_trans ?_ (sum_le_sum hcos)
  rw [sum_sub_distrib, ← sum_div]
  have hsq : ∑ j ∈ range m, (((j : ℝ) - ((m : ℝ) - 1) / 2) * θ) ^ 2 =
      θ ^ 2 * (m * ((m : ℝ) ^ 2 - 1) / 12) := by
    simp_rw [mul_pow]
    rw [← sum_mul, sumSq]; ring
  rw [hsq]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  nlinarith

lemma bitsToNat_natToBits (n k : ℕ) : bitsToNat (natToBits n k) = k % 2 ^ n := by
  rw [← bitsEquivFin_apply, natToBits, Equiv.apply_symm_apply]

lemma natToBits_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : natToBits n x = natToBits n y) : x = y := by
  have := congrArg bitsToNat h
  rwa [bitsToNat_natToBits, bitsToNat_natToBits, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

lemma bitsToNat_zero (n : ℕ) : bitsToNat (0 : Qubits n) = 0 := by
  simp [bitsToNat]

lemma sum_qubits {M : Type*} [AddCommMonoid M] (ℓ : ℕ) (h : ℕ → M) :
    ∑ a : Qubits ℓ, h (bitsToNat a) = ∑ k ∈ range (2 ^ ℓ), h k := by
  calc ∑ a : Qubits ℓ, h (bitsToNat a)
        = ∑ a : Qubits ℓ, (fun k : Fin (2 ^ ℓ) => h k) (bitsEquivFin ℓ a) := by
          simp only [bitsEquivFin_apply]
    _ = ∑ k : Fin (2 ^ ℓ), h k := Equiv.sum_comp (bitsEquivFin ℓ) (fun k : Fin (2 ^ ℓ) => h k)
    _ = ∑ k ∈ range (2 ^ ℓ), h k := Fin.sum_univ_eq_sum_range h _

lemma amp (ℓ n : ℕ) (g : Qubits ℓ → Qubits n) (b : Qubits ℓ) (y : Qubits n) :
    (act (Matrix.kronecker (qftQubits ℓ) (1 : Matrix (Qubits n) (Qubits n) ℂ) * xorOracle g *
      Matrix.kronecker (qftQubits ℓ) (1 : Matrix (Qubits n) (Qubits n) ℂ)) (ket (0, 0))) (b, y) =
    ∑ a : Qubits ℓ, if y = g a then qftQubits ℓ b a * qftQubits ℓ a 0 else 0 := by
  simp [act, ket, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, xorOracle]
  refine Fintype.sum_congr _ _ (fun a => ?_)
  simp only [ite_and]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [hx]),
    Fintype.sum_eq_single (g a) (fun x hx => by simp [hx])]
  split_ifs <;> simp_all

lemma cond_iff (N r : ℕ) (f : ℕ → ℕ) (hf : ∀ a, f a < N) (hP : HasPeriod f r) (s k : ℕ)
    (hs : s < r) :
    natToBits (Nat.clog 2 N) (f s) = natToBits (Nat.clog 2 N) (f k) ↔ k % r = s := by
  have hN : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog one_lt_two N
  constructor
  · intro h
    have := natToBits_inj (lt_of_lt_of_le (hf s) hN) (lt_of_lt_of_le (hf k) hN) h
    have h2 := (hP s k).1 this
    unfold Nat.ModEq at h2; rw [Nat.mod_eq_of_lt hs] at h2; exact h2.symm
  · intro h
    have : f s = f k := (hP s k).2 (by unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hs, h])
    rw [this]

lemma sum_filter_mod {M : Type*} [AddCommMonoid M] (q r s : ℕ) (hr : 0 < r) (hs : s < r)
    (hsq : s < q) (F : ℕ → M) :
    ∑ k ∈ range q, (if k % r = s then F k else 0) =
      ∑ j ∈ range ((q - 1 - s) / r + 1), F (s + j * r) := by
  rw [← sum_filter]
  apply Finset.sum_nbij' (fun k => k / r) (fun j => s + j * r)
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    have e := Nat.mod_add_div' k r
    rw [hk.2] at e
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hr]; omega
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hr] at hj
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have e := Nat.mod_add_div' k r; rw [hk.2] at e; exact e
  · intro j _
    rw [Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hs, zero_add]
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have e := Nat.mod_add_div' k r; rw [hk.2] at e; rw [e]

lemma q_ge (N r : ℕ) (hN : 16 ≤ N) (hrN : r ≤ N) : 16 * r ≤ 2 ^ shorEll N := by
  have := Nat.le_pow_clog one_lt_two (N ^ 2 + 1)
  unfold shorEll
  nlinarith

lemma prob_ge (N r : ℕ) (f : ℕ → ℕ) (hN : 16 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hf : ∀ a, f a < N) (hP : HasPeriod f r) (b0 c s : ℕ) (hb0 : b0 < 2 ^ shorEll N)
    (hbc : |(b0 : ℝ) * r - c * ((2 ^ shorEll N : ℕ) : ℝ)| ≤ r / 2) (hs : s < r) :
    1 / (16 * (r : ℝ) ^ 2) ≤
      prob (shorRunState N f) (natToBits (shorEll N) b0, natToBits (Nat.clog 2 N) (f s)) := by
  set ℓ := shorEll N with hℓ
  set n := Nat.clog 2 N with hn
  set q := 2 ^ ℓ with hq
  have hq16 : 16 * r ≤ q := q_ge N r hN hrN
  have hqpos : 0 < q := by positivity
  set m := (q - 1 - s) / r + 1 with hm
  set E : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / ((q : ℕ) : ℂ))
    with hE
  have hsqrt : ((Real.sqrt (q : ℕ) : ℝ) : ℂ) * ((Real.sqrt (q : ℕ) : ℝ) : ℂ) = ((q : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hsum : (∑ a : Qubits ℓ, if natToBits n (f s) = natToBits n (f (bitsToNat a)) then
      qftQubits ℓ (natToBits ℓ b0) a * qftQubits ℓ a 0 else 0) =
      (1 / ((q : ℕ) : ℂ)) * ∑ j ∈ range m, E (b0 * (s + j * r)) := by
    have hterm : ∀ a : Qubits ℓ, (if natToBits n (f s) = natToBits n (f (bitsToNat a)) then
        qftQubits ℓ (natToBits ℓ b0) a * qftQubits ℓ a 0 else 0) =
        (1 / ((q : ℕ) : ℂ)) * (fun k => if k % r = s then E (b0 * k) else 0) (bitsToNat a) := by
      intro a
      by_cases h : bitsToNat a % r = s
      · rw [if_pos ((cond_iff N r f hf hP s _ hs).2 h)]
        show _ = 1 / ((q : ℕ) : ℂ) * (if bitsToNat a % r = s then E (b0 * bitsToNat a) else 0)
        rw [if_pos h]
        have e1 : qftQubits ℓ (natToBits ℓ b0) a = E (b0 * bitsToNat a) / (Real.sqrt (q : ℕ) : ℂ) := by
          rw [qftQubits, Matrix.submatrix_apply, qftMatrix_apply, bitsEquivFin_apply,
            bitsEquivFin_apply, bitsToNat_natToBits, Nat.mod_eq_of_lt hb0]
        have e2 : qftQubits ℓ a 0 = 1 / (Real.sqrt (q : ℕ) : ℂ) := by
          rw [qftQubits, Matrix.submatrix_apply, qftMatrix_apply, bitsEquivFin_apply,
            bitsEquivFin_apply, bitsToNat_zero]
          simp [hq]
        rw [e1, e2, div_mul_div_comm, mul_one, hsqrt]; ring
      · rw [if_neg (fun h' => h ((cond_iff N r f hf hP s _ hs).1 h'))]
        show _ = 1 / ((q : ℕ) : ℂ) * (if bitsToNat a % r = s then E (b0 * bitsToNat a) else 0)
        rw [if_neg h, mul_zero]
    rw [Fintype.sum_congr _ _ hterm, ← mul_sum, sum_qubits ℓ (fun k => if k % r = s then E (b0 * k) else 0),
      sum_filter_mod q r s (by omega) hs (by omega)]
  have hgeo := geo q r b0 s c m hqpos (Nat.le_add_left _ _) (by
      rw [hm, Nat.add_sub_cancel]; exact (Nat.div_mul_le_self _ _).trans (by omega)) hq16 hbc
  have hmr : q ≤ 2 * (m * r) := by
    have := Nat.lt_div_mul_add (a := q - 1 - s) (b := r) (by omega)
    rw [hm, Nat.add_mul, one_mul]; omega
  simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [shorRunState, amp, hsum, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hmr' : (q : ℝ) ≤ 2 * (m * r) := by exact_mod_cast hmr
  have h1 : 1 / (4 * (r : ℝ)) ≤ 1 / (q : ℝ) * ‖∑ j ∈ range m, E (b0 * (s + j * r))‖ := by
    rw [hE]
    calc 1 / (4 * (r : ℝ)) ≤ 1 / (q : ℝ) * ((m : ℝ) / 2) := by
          rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith
      _ ≤ _ := by gcongr
  calc 1 / (16 * (r : ℝ) ^ 2) = (1 / (4 * (r : ℝ))) ^ 2 := by ring
    _ ≤ _ := by gcongr

open Classical in
lemma probEvent_ge (N r : ℕ) (f : ℕ → ℕ) (hN : 16 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hf : ∀ a, f a < N) (hP : HasPeriod f r) :
    (Nat.totient r : ℝ) / (16 * r) ≤ probEvent (shorRunState N f) fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N) := by
  set ℓ := shorEll N with hℓ
  set n := Nat.clog 2 N with hn
  set q := 2 ^ ℓ with hq
  have hq16 : 16 * r ≤ q := q_ge N r hN hrN
  have hqpos : 0 < q := by positivity
  set bc : ℕ → ℕ := fun c => (2 * c * q + r) / (2 * r) with hbcdef
  have hbc1 : ∀ c, bc c * (2 * r) ≤ 2 * c * q + r := fun c => Nat.div_mul_le_self _ _
  have hbc2 : ∀ c, 2 * c * q + r < bc c * (2 * r) + 2 * r := fun c =>
    Nat.lt_div_mul_add (a := 2 * c * q + r) (b := 2 * r) (by omega)
  have hbclt : ∀ c, c < r → bc c < q := by
    intro c hc
    by_contra h; push Not at h
    have := hbc1 c
    nlinarith
  have hbcabs : ∀ c, |(bc c : ℝ) * r - c * ((q : ℕ) : ℝ)| ≤ r / 2 := by
    intro c
    have h1 : ((bc c * (2 * r) : ℕ) : ℝ) ≤ ((2 * c * q + r : ℕ) : ℝ) := by exact_mod_cast hbc1 c
    have h2 : ((2 * c * q + r : ℕ) : ℝ) < ((bc c * (2 * r) + 2 * r : ℕ) : ℝ) := by
      exact_mod_cast hbc2 c
    push_cast at h1 h2
    rw [abs_le]; constructor <;> nlinarith
  have hbcinj : ∀ c c', c < r → c' < r → bc c = bc c' → c = c' := by
    intro c c' hc hc' h
    have a1 := hbc1 c; have a2 := hbc2 c; have a3 := hbc1 c'; have a4 := hbc2 c'
    rw [h] at a1 a2
    have l1 : c * q < (c' + 1) * q := by nlinarith
    have l2 : c' * q < (c + 1) * q := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right l1; have := Nat.lt_of_mul_lt_mul_right l2; omega
  set Cs := (range r).filter (fun c => Nat.Coprime r c) with hCs
  set φm : ℕ × ℕ → Qubits ℓ × Qubits n := fun x => (natToBits ℓ (bc x.1), natToBits n (f x.2))
    with hφm
  have hN2 : N ≤ 2 ^ n := Nat.le_pow_clog one_lt_two N
  have hinj : Set.InjOn φm ↑(Cs ×ˢ range r) := by
    rintro ⟨c, s⟩ hx ⟨c', s'⟩ hx' h
    simp only [hCs, coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq, coe_range,
      Set.mem_Iio] at hx hx'
    simp only [hφm, Prod.mk.injEq] at h
    have e1 := hbcinj c c' hx.1.1 hx'.1.1 (natToBits_inj (hbclt c hx.1.1) (hbclt c' hx'.1.1) h.1)
    have e2 := (cond_iff N r f hf hP s s' hx.2).1 h.2
    rw [Nat.mod_eq_of_lt hx'.2] at e2
    rw [e1, e2]
  have hQ : ((q : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by rw [hq]; push_cast; rfl
  have hsub : (Cs ×ˢ range r).image φm ⊆ univ.filter (fun z : Qubits ℓ × Qubits n =>
      ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ ℓ - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ ℓ)) := by
    intro z hz
    rw [mem_image] at hz
    obtain ⟨⟨c, s⟩, hx, rfl⟩ := hz
    simp only [hCs, mem_product, mem_filter, mem_range] at hx
    simp only [mem_filter, mem_univ, true_and, hφm]
    refine ⟨c, hx.1.1, hx.1.2.symm, ?_⟩
    rw [bitsToNat_natToBits, Nat.mod_eq_of_lt (hbclt c hx.1.1)]
    have hQp : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hb := hbcabs c
    rw [hQ] at hb
    rw [div_sub_div _ _ hQp.ne' hr0.ne', abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ ℓ * r),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have e : |(bc c : ℝ) * r - (2 : ℝ) ^ ℓ * c| = |(bc c : ℝ) * r - c * (2 : ℝ) ^ ℓ| := by
      ring_nf
    rw [e]
    nlinarith [abs_nonneg ((bc c : ℝ) * r - c * (2 : ℝ) ^ ℓ)]
  have hnn : ∀ z, 0 ≤ prob (shorRunState N f) z := fun z => by unfold prob; positivity
  unfold probEvent
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  calc (Nat.totient r : ℝ) / (16 * r)
      = ∑ c ∈ Cs, ∑ s ∈ range r, 1 / (16 * (r : ℝ) ^ 2) := by
        simp only [sum_const, card_range, nsmul_eq_mul, hCs, ← Nat.totient_eq_card_coprime]
        field_simp
    _ ≤ ∑ c ∈ Cs, ∑ s ∈ range r, prob (shorRunState N f) (φm (c, s)) := by
        apply sum_le_sum; intro c hc; apply sum_le_sum; intro s hs
        simp only [hCs, mem_filter, mem_range] at hc hs
        exact prob_ge N r f hN hr hrN hf hP (bc c) c s (hbclt c hc.1) (hbcabs c) hs
    _ = ∑ x ∈ Cs ×ˢ range r, prob (shorRunState N f) (φm x) :=
        (sum_product Cs (range r) (fun x => prob (shorRunState N f) (φm x))).symm
    _ = ∑ z ∈ (Cs ×ˢ range r).image φm, prob (shorRunState N f) z := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hnn z)

lemma part2 : ∀ N r c b : ℕ, 1 ≤ r → r ≤ N → c < r → Nat.Coprime c r →
      |(b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
        ((c : ℚ) / r).den = r ∧
        ∀ (p : ℤ) (s : ℕ), 1 ≤ s → s ≤ N →
          |(b : ℝ) / (2 : ℝ) ^ shorEll N - (p : ℝ) / s| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
            (p : ℝ) / s = (c : ℝ) / r := by
  intro N r c b hr hrN hc hcop h
  constructor
  · have := Rat.den_div_eq_of_coprime (a := (c : ℤ)) (b := (r : ℤ)) (by omega) (by simpa using hcop)
    have e : ((c : ℤ) : ℚ) / ((r : ℤ) : ℚ) = (c : ℚ) / r := by push_cast; rfl
    rw [e] at this; exact_mod_cast this
  · intro p s hs hsN h'
    set Q := (2 : ℝ) ^ shorEll N with hQdef
    have hQ : (N : ℝ) ^ 2 < Q := by
      have h1 := Nat.le_pow_clog one_lt_two (N ^ 2 + 1)
      have h2 : ((N ^ 2 + 1 : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (N ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2; rw [hQdef, shorEll]; linarith
    have hQpos : 0 < Q := by positivity
    have htri : |(p : ℝ) / s - c / r| ≤ 1 / Q := by
      calc |(p : ℝ) / s - c / r| = |((b : ℝ) / Q - c / r) - ((b : ℝ) / Q - p / s)| := by ring_nf
        _ ≤ |(b : ℝ) / Q - c / r| + |(b : ℝ) / Q - p / s| := abs_sub _ _
        _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := add_le_add h h'
        _ = 1 / Q := by field_simp; ring
    by_contra hne
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hD : p * (r : ℤ) - c * s ≠ 0 := by
      intro hD
      apply hne
      rw [div_eq_div_iff hs0.ne' hr0.ne']
      have : ((p * (r : ℤ) - c * s : ℤ) : ℝ) = 0 := by exact_mod_cast hD
      push_cast at this; linarith
    have h1 : (1 : ℝ) ≤ |((p * (r : ℤ) - c * s : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hD
    have e : (p : ℝ) / s - c / r = ((p * (r : ℤ) - c * s : ℤ) : ℝ) / (s * r) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s * r)] at htri
    have hsr : (s : ℝ) * r ≤ (N : ℝ) ^ 2 := by
      have : (s : ℝ) ≤ N := by exact_mod_cast hsN
      have : (r : ℝ) ≤ N := by exact_mod_cast hrN
      nlinarith
    rw [div_le_div_iff₀ (by positivity) hQpos] at htri
    nlinarith

end ShorQ

open QAlgorithms in
open Classical in
theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ a, f a < N) → HasPeriod f r →
        C / Real.log (Real.log N) ≤ probEvent (shorRunState N f) fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) ∧
    (∀ N r c b : ℕ, 1 ≤ r → r ≤ N → c < r → Nat.Coprime c r →
      |(b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
        ((c : ℚ) / r).den = r ∧
        ∀ (p : ℤ) (s : ℕ), 1 ≤ s → s ≤ N →
          |(b : ℝ) / (2 : ℝ) ^ shorEll N - (p : ℝ) / s| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
            (p : ℝ) / s = (c : ℝ) / r) := by
  refine ⟨?_, ShorQ.part2⟩
  obtain ⟨C0, hC0, hNT⟩ := ShorNT.totient_lower
  refine ⟨C0 / 16, by positivity, 256, fun N hN r hr hrN f hf hP => ?_⟩
  have h1 := hNT N hN r hr hrN
  have h2 := ShorQ.probEvent_ge N r f (by omega) hr hrN hf hP
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  calc C0 / 16 / Real.log (Real.log N) = (C0 / Real.log (Real.log N)) / 16 := by ring
    _ ≤ ((Nat.totient r : ℝ) / r) / 16 := by gcongr
    _ = (Nat.totient r : ℝ) / (16 * r) := by field_simp
    _ ≤ _ := h2
