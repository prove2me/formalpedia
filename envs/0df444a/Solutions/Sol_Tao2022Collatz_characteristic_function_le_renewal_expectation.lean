-- Prove2me | solution 1 for Tao2022Collatz.characteristic_function_le_renewal_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:24:10.651262+00:00
-- url     : https://prove2.me/submissions/96e5fe0e-dc9c-47a1-8207-2e002bd5dc3e

import Mathlib

set_option autoImplicit false

/-! Tao arXiv:1909.03562, Section 7 layer (item 8). Self-contained copy of the `_syr` definitions
`ps`, `Fnat`, `padv`, `syrZ`, `Box`, `chi`, `Prop117` (identical text), plus:
* 8a: the white-point reduction (Tao (7.5) + Lemma 7.2): `‖chi n K ξ‖ ≤ Vt n K ξ ε (n/2) 0 0`, where `Vt` is the
  finite form of Tao's `E exp(-ε^3 #{j : b_j = 3, (j, b_[1,j]) ∈ W})` written as the recursion (7.35) over pairs
  `(a_{2j-1}, a_{2j}) ∈ [1,K]^2`; and `Prop73 → Prop117`. -/

namespace Tao31

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

lemma ps_add (a : ℕ → ℕ) (p q : ℕ) : ps a (p + q) = ps a p + ps (fun i => a (p + i)) q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [← add_assoc, ps_succ, ih, ps_succ, add_assoc]

def Fnat (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, 3 ^ j * 2 ^ (ps a n - ps a (j + 1))

def padv {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then w ⟨i, h⟩ else 1

noncomputable def syrZ (n : ℕ) (a : ℕ → ℕ) : ZMod (3 ^ n) :=
  (Fnat a n : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a n

noncomputable def Box (n K : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 K)

noncomputable def chi (n K : ℕ) (ξ : ℤ) : ℂ :=
  ∑ w ∈ Box n K, ((1 : ℂ) / 2) ^ (∑ i, w i) *
    Complex.exp (-(2 * Real.pi * Complex.I) * ξ * ((syrZ n (padv w)).val : ℂ) / 3 ^ n)

def Prop117 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖chi n K ξ‖ ≤ C * (n : ℝ) ^ (-A)

lemma two_mul_inv (n : ℕ) : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
  have hc : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 hc
  simpa using this

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

/-! ### 8a.1 Fixed-modulus offsets and the two-step recursion -/

/-- `Σ_{j<m} 3^j 2^{-a_{[1,j+1]}}` in the fixed ring `ZMod (3^n)`. -/
noncomputable def Sm (n m : ℕ) (a : ℕ → ℕ) : ZMod (3 ^ n) :=
  ∑ j ∈ Finset.range m, (3 : ZMod (3 ^ n)) ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a (j + 1)

lemma Sm_congr (n m : ℕ) (a b : ℕ → ℕ) (h : ∀ i < m, a i = b i) : Sm n m a = Sm n m b := by
  unfold Sm
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [ps_congr a b (j + 1) (fun i hi => h i (by omega))]

lemma syrZ_eq_Sm (n : ℕ) (a : ℕ → ℕ) : syrZ n a = Sm n n a := by
  unfold syrZ Sm Fnat
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hle : ps a (j + 1) ≤ ps a n := ps_mono a (by omega)
  obtain ⟨d, hd⟩ : ∃ d, ps a n = ps a (j + 1) + d := ⟨ps a n - ps a (j + 1), by omega⟩
  rw [hd, Nat.add_sub_cancel_left, pow_add ((2 : ZMod (3 ^ n))⁻¹)]
  have h2 : (2 : ZMod (3 ^ n)) ^ d * ((2 : ZMod (3 ^ n))⁻¹) ^ d = 1 := by
    rw [← mul_pow, two_mul_inv, one_pow]
  linear_combination (3 : ZMod (3 ^ n)) ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a (j + 1) * h2

lemma Sm_split2 (n m : ℕ) (a : ℕ → ℕ) :
    Sm n (2 + m) a = ((2 : ZMod (3 ^ n))⁻¹) ^ a 0 + 3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (a 0 + a 1) +
      9 * ((2 : ZMod (3 ^ n))⁻¹) ^ (a 0 + a 1) * Sm n m (fun i => a (2 + i)) := by
  unfold Sm
  rw [Finset.sum_range_add, Finset.mul_sum]
  have h2 : ps a 2 = a 0 + a 1 := by simp [ps]
  congr 1
  · simp [Finset.sum_range_succ, ps]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show 2 + j + 1 = 2 + (j + 1) by ring, ps_add, h2, pow_add, pow_add]
    ring

/-- The character sum over `[1,K]^m` at a fixed modulus `3^n`, frequency `x`. -/
noncomputable def Phi (n m K : ℕ) (x : ZMod (3 ^ n)) : ℂ :=
  ∑ w ∈ Box m K, ((1 : ℂ) / 2) ^ (∑ i, w i) * ZMod.stdAddChar (x * Sm n m (padv w))

lemma chi_eq_Phi (n K : ℕ) (ξ : ℤ) : chi n K ξ = Phi n n K (-(ξ : ZMod (3 ^ n))) := by
  rw [chi_eq]
  unfold Phi
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [syrZ_eq_Sm]

lemma norm_Phi_le_one (n m K : ℕ) (x : ZMod (3 ^ n)) : ‖Phi n m K x‖ ≤ 1 := by
  unfold Phi
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (le_of_eq ?_) (box_mass_le m K)
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [norm_mul, AddChar.norm_apply, mul_one, norm_pow, norm_div, norm_one, Complex.norm_two]

/-- Left / right blocks of a tuple of length `k + q`. -/
def lft {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin k → ℕ := fun i => w (Fin.castAdd q i)
def rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin q → ℕ := fun i => w (Fin.natAdd k i)

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

/-- Tao (7.4) before taking norms: peel off the first pair `(a_1, a_2)`. -/
theorem Phi_split2 (n m K : ℕ) (x : ZMod (3 ^ n)) :
    Phi n (2 + m) K x = ∑ u ∈ Box 2 K, ((1 : ℂ) / 2) ^ (∑ i, u i) *
      ZMod.stdAddChar (x * (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 + 3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) *
        Phi n m K (x * 9 * ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i, u i)) := by
  unfold Phi
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
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
    have h0 : padv w 0 = lft w 0 := by
      unfold padv lft; rw [dif_pos (by omega)]; congr 1
    have h1 : padv w 1 = lft w 1 := by
      unfold padv lft; rw [dif_pos (by omega)]; congr 1
    have hs : (∑ i, lft w i) = lft w 0 + lft w 1 := Fin.sum_univ_two _
    have hr : Sm n m (fun i => padv w (2 + i)) = Sm n m (padv (rgt w)) := by
      apply Sm_congr
      intro i hi
      simp only [padv, rgt]
      rw [dif_pos (by omega), dif_pos hi]
      rfl
    rw [Sm_split2, h0, h1, hr, sum_lft_rgt w, pow_add ((1 : ℂ) / 2), hs]
    have hx : x * (((2 : ZMod (3 ^ n))⁻¹) ^ lft w 0 + 3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (lft w 0 + lft w 1) +
        9 * ((2 : ZMod (3 ^ n))⁻¹) ^ (lft w 0 + lft w 1) * Sm n m (padv (rgt w))) =
        x * (((2 : ZMod (3 ^ n))⁻¹) ^ lft w 0 + 3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (lft w 0 + lft w 1)) +
        x * 9 * ((2 : ZMod (3 ^ n))⁻¹) ^ (lft w 0 + lft w 1) * Sm n m (padv (rgt w)) := by ring
    rw [hx, AddChar.map_add_eq_mul]
    ring

/-! ### 8a.2 Lemma 7.2 (cancellation at white points) -/

lemma norm_one_add_exp (θ : ℝ) :
    ‖1 + Complex.exp (2 * (θ : ℂ) * Complex.I)‖ = 2 * |Real.cos θ| := by
  have h : 1 + Complex.exp (2 * (θ : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * (2 * Complex.cos θ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_two_mul, Complex.sin_two_mul]
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_two,
    ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]

lemma abs_cos_pi_le (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    |Real.cos (Real.pi * s)| ≤ 1 - 2 * s ^ 2 := by
  have hc0 : 0 ≤ Real.cos (Real.pi * s) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  rw [abs_of_nonneg hc0]
  have hb := Real.cos_le_one_sub_mul_cos_sq (x := Real.pi * s)
    (by rw [abs_of_nonneg (by positivity)]; nlinarith [Real.pi_pos])
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  calc Real.cos (Real.pi * s) ≤ 1 - 2 / Real.pi ^ 2 * (Real.pi * s) ^ 2 := hb
    _ = 1 - 2 * s ^ 2 := by field_simp

lemma abs_cos_white (ε t : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (h1 : ε < t) (h2 : t < 1 - ε) :
    |Real.cos (Real.pi * t)| ≤ Real.exp (-ε ^ 3) := by
  have key : |Real.cos (Real.pi * t)| ≤ 1 - 2 * ε ^ 2 := by
    rcases le_or_gt t (1 / 2) with ht | ht
    · refine (abs_cos_pi_le t (by linarith) ht).trans ?_
      nlinarith
    · have he : Real.cos (Real.pi * t) = -Real.cos (Real.pi * (1 - t)) := by
        rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.cos_pi_sub, neg_neg]
      rw [he, abs_neg]
      refine (abs_cos_pi_le (1 - t) (by linarith) (by linarith)).trans ?_
      nlinarith
  refine key.trans ?_
  have hx := Real.add_one_le_exp (-ε ^ 3)
  have : ε ^ 3 ≤ 2 * ε ^ 2 := by nlinarith [sq_nonneg ε]
  linarith

/-- Tao's `θ(J,L) = ξ 3^{2J-2} 2^{-L+1} mod 3^n` (7.8), as an element of `ZMod (3^n)`. -/
noncomputable def thZ (n : ℕ) (ξ : ℤ) (J L : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 9 ^ (J - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (L - 1)

/-- `(J, L)` is white (7.9): the signed fractional part of `θ(J,L)/3^n` exceeds `ε` in size. -/
def White (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L : ℕ) : Prop :=
  ε * 3 ^ n < ((thZ n ξ J L).val : ℝ) ∧ ((thZ n ξ J L).val : ℝ) < (1 - ε) * 3 ^ n

lemma norm_one_add_char_white (n : ℕ) (z : ZMod (3 ^ n)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h1 : ε * 3 ^ n < (z.val : ℝ)) (h2 : (z.val : ℝ) < (1 - ε) * 3 ^ n) :
    ‖1 + (ZMod.stdAddChar (-z) : ℂ)‖ ≤ 2 * Real.exp (-ε ^ 3) := by
  have hN : (0 : ℝ) < 3 ^ n := by positivity
  set t : ℝ := (z.val : ℝ) / 3 ^ n with ht
  have ht1 : ε < t := by rw [ht, lt_div_iff₀ hN]; exact h1
  have ht2 : t < 1 - ε := by rw [ht, div_lt_iff₀ hN]; exact h2
  have hconj : ‖1 + (ZMod.stdAddChar (-z) : ℂ)‖ = ‖1 + (ZMod.stdAddChar z : ℂ)‖ := by
    rw [AddChar.map_neg_eq_conj, ← Complex.norm_conj (1 + (ZMod.stdAddChar z : ℂ)), map_add, map_one]
  rw [hconj, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (z.val : ℂ) / ((3 ^ n : ℕ) : ℂ) =
      2 * ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    rw [ht]; push_cast; field_simp
  rw [he, norm_one_add_exp]
  have := abs_cos_white ε t hε hε1 ht1 ht2
  linarith

/-! ### 8a.3 The renewal majorant `Vt` and the reduction `‖chi‖ ≤ Vt` -/

open Classical in
/-- The factor `exp(-ε^3 1_W(J,L))` applied at a pair with sum `b = 3`. -/
noncomputable def cf (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L b : ℕ) : ℝ :=
  if b = 3 ∧ White n ξ ε J L then Real.exp (-ε ^ 3) else 1

/-- Tao's `Q`-recursion (7.35) in finite form: `r` remaining pairs, current position `(j, l)`
(`j` pairs done, `l = b_{[1,j]}`). `Vt n K ξ ε (n/2) 0 0` is the left side of (7.10) for `[1,K]`-truncated pairs. -/
noncomputable def Vt (n K : ℕ) (ξ : ℤ) (ε : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | r + 1, j, l => ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
      cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * Vt n K ξ ε r (j + 1) (l + ∑ i, u i)

lemma cf_nonneg (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L b : ℕ) : 0 ≤ cf n ξ ε J L b := by
  unfold cf; split_ifs <;> positivity

lemma Vt_nonneg (n K : ℕ) (ξ : ℤ) (ε : ℝ) : ∀ r j l, 0 ≤ Vt n K ξ ε r j l
  | 0, _, _ => by simp [Vt]
  | r + 1, j, l => by
    simp only [Vt]
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (mul_nonneg (by positivity) (cf_nonneg _ _ _ _ _ _))
      (Vt_nonneg n K ξ ε r _ _))

lemma box2_three (K : ℕ) (hK : 2 ≤ K) :
    (Box 2 K).filter (fun u => ∑ i, u i = 3) = {![1, 2], ![2, 1]} := by
  ext u
  simp only [Finset.mem_filter, Box, Fintype.mem_piFinset, Finset.mem_Icc, Fin.sum_univ_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hs⟩
    have h0 := hb 0
    have h1 := hb 1
    rcases (by omega : (u 0 = 1 ∧ u 1 = 2) ∨ (u 0 = 2 ∧ u 1 = 1)) with h | h
    · left; funext i; fin_cases i <;> simp [h.1, h.2]
    · right; funext i; fin_cases i <;> simp [h.1, h.2]
  · rintro (rfl | rfl)
    · refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega
    · refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega

lemma box2_three_small (K : ℕ) (hK : K < 2) :
    (Box 2 K).filter (fun u => ∑ i, u i = 3) = ∅ := by
  ext u
  simp only [Finset.mem_filter, Box, Fintype.mem_piFinset, Finset.mem_Icc, Fin.sum_univ_two,
    Finset.notMem_empty, iff_false, not_and]
  intro hb hs
  have h0 := hb 0
  have h1 := hb 1
  omega

/-- The `b = 3` pair sum (Tao Lemma 7.2): `‖Σ_{a_1+a_2=3} e(x(2^{-a_1} + 3·2^{-3}))‖ ≤ #·cf`. -/
lemma pair3_bound (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j l : ℕ) :
    ‖∑ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
        (ZMod.stdAddChar ((-(ξ : ZMod (3 ^ n)) * 9 ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ l) *
          (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 + 3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) : ℂ)‖ ≤
      ((Box 2 K).filter (fun u => ∑ i, u i = 3)).card * cf n ξ ε (j + 1) (l + 3) 3 := by
  set x : ZMod (3 ^ n) := -(ξ : ZMod (3 ^ n)) * 9 ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ l with hx
  by_cases hW : White n ξ ε (j + 1) (l + 3)
  · rcases le_or_gt 2 K with hK | hK
    · rw [box2_three K hK]
      have hne : (![1, 2] : Fin 2 → ℕ) ≠ ![2, 1] := by
        intro h; have := congrFun h 0; simp at this
      rw [Finset.sum_pair hne, Finset.card_pair hne]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcf : cf n ξ ε (j + 1) (l + 3) 3 = Real.exp (-ε ^ 3) := by
        unfold cf; rw [if_pos ⟨rfl, hW⟩]
      rw [hcf]
      set i2 : ZMod (3 ^ n) := (2 : ZMod (3 ^ n))⁻¹
      have hi : (2 : ZMod (3 ^ n)) * i2 = 1 := two_mul_inv n
      have hsplit : x * (i2 ^ 1 + 3 * i2 ^ (1 + 2)) =
          x * (i2 ^ 2 + 3 * i2 ^ (2 + 1)) + (-(thZ n ξ (j + 1) (l + 3))) := by
        unfold thZ
        simp only [Nat.add_sub_cancel, show l + 3 - 1 = l + 2 by omega, hx]
        linear_combination ((ξ : ZMod (3 ^ n)) * 9 ^ j * i2 ^ l * i2) * hi
      rw [hsplit, AddChar.map_add_eq_mul]
      have hfac : (ZMod.stdAddChar (x * (i2 ^ 2 + 3 * i2 ^ (2 + 1))) : ℂ) *
            ZMod.stdAddChar (-thZ n ξ (j + 1) (l + 3)) +
          ZMod.stdAddChar (x * (i2 ^ 2 + 3 * i2 ^ (2 + 1))) =
          ZMod.stdAddChar (x * (i2 ^ 2 + 3 * i2 ^ (2 + 1))) *
            (1 + ZMod.stdAddChar (-thZ n ξ (j + 1) (l + 3))) := by ring
      rw [hfac, norm_mul, AddChar.norm_apply, one_mul]
      have := norm_one_add_char_white n (thZ n ξ (j + 1) (l + 3)) ε hε hε1 hW.1 hW.2
      push_cast
      linarith
    · rw [box2_three_small K hK]; simp
  · have hcf : cf n ξ ε (j + 1) (l + 3) 3 = 1 := by
      unfold cf; rw [if_neg (fun h => hW h.2)]
    rw [hcf, mul_one]
    refine (norm_sum_le _ _).trans ?_
    simp [AddChar.norm_apply]

/-- 8a: `‖Phi‖` along the renewal process is bounded by the majorant `Vt` (Tao (7.5) + Lemma 7.2). -/
theorem norm_Phi_le_Vt (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ m j l : ℕ, ‖Phi n m K (-(ξ : ZMod (3 ^ n)) * 9 ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ l)‖ ≤
      Vt n K ξ ε (m / 2) j l := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j l
  rcases Nat.lt_or_ge m 2 with hm | hm2
  · rw [show m / 2 = 0 by omega]
    simp only [Vt]
    exact norm_Phi_le_one _ _ _ _
  · obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
    rw [show (2 + m') / 2 = m' / 2 + 1 by omega, Phi_split2]
    simp only [Vt]
    set x : ZMod (3 ^ n) := -(ξ : ZMod (3 ^ n)) * 9 ^ j * ((2 : ZMod (3 ^ n))⁻¹) ^ l with hx
    have hP : ∀ b : ℕ, x * 9 * ((2 : ZMod (3 ^ n))⁻¹) ^ b =
        -(ξ : ZMod (3 ^ n)) * 9 ^ (j + 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + b) := by
      intro b; rw [hx]; ring
    simp_rw [hP]
    have IH : ∀ b : ℕ, ‖Phi n m' K (-(ξ : ZMod (3 ^ n)) * 9 ^ (j + 1) *
        ((2 : ZMod (3 ^ n))⁻¹) ^ (l + b))‖ ≤ Vt n K ξ ε (m' / 2) (j + 1) (l + b) :=
      fun b => ih m' (by omega) (j + 1) (l + b)
    rw [← Finset.sum_filter_add_sum_filter_not (Box 2 K) (fun u => ∑ i, u i = 3),
      ← Finset.sum_filter_add_sum_filter_not (Box 2 K) (fun u => ∑ i, u i = 3)]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · -- the `b = 3` pairs
      have hL : ∀ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
          ((1 : ℂ) / 2) ^ (∑ i, u i) * ZMod.stdAddChar (x * (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 +
            3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) *
            Phi n m' K (-(ξ : ZMod (3 ^ n)) * 9 ^ (j + 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i)) =
          (((1 : ℂ) / 2) ^ 3 * Phi n m' K (-(ξ : ZMod (3 ^ n)) * 9 ^ (j + 1) *
            ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3))) *
            ZMod.stdAddChar (x * (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 +
              3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) := by
        intro u hu
        rw [(Finset.mem_filter.1 hu).2]; ring
      have hR : ∀ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
          ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) *
            Vt n K ξ ε (m' / 2) (j + 1) (l + ∑ i, u i) =
          ((1 : ℝ) / 2) ^ 3 * cf n ξ ε (j + 1) (l + 3) 3 * Vt n K ξ ε (m' / 2) (j + 1) (l + 3) := by
        intro u hu
        rw [(Finset.mem_filter.1 hu).2]
      rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.mul_sum, norm_mul, norm_mul,
        Finset.sum_const, nsmul_eq_mul]
      have hpb := pair3_bound n K ξ ε hε hε1 j l
      rw [← hx] at hpb
      have h8 : ‖((1 : ℂ) / 2) ^ 3‖ = ((1 : ℝ) / 2) ^ 3 := by
        rw [norm_pow, norm_div, norm_one, Complex.norm_two]
      rw [h8]
      have hV0 := Vt_nonneg n K ξ ε (m' / 2) (j + 1) (l + 3)
      have hcf0 := cf_nonneg n ξ ε (j + 1) (l + 3) 3
      have hn0 := norm_nonneg (∑ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
        (ZMod.stdAddChar (x * (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 +
          3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) : ℂ))
      have hI := IH 3
      calc ((1 : ℝ) / 2) ^ 3 * ‖Phi n m' K (-(ξ : ZMod (3 ^ n)) * 9 ^ (j + 1) *
              ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3))‖ *
            ‖∑ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
              (ZMod.stdAddChar (x * (((2 : ZMod (3 ^ n))⁻¹) ^ u 0 +
                3 * ((2 : ZMod (3 ^ n))⁻¹) ^ (u 0 + u 1))) : ℂ)‖
          ≤ ((1 : ℝ) / 2) ^ 3 * Vt n K ξ ε (m' / 2) (j + 1) (l + 3) *
            (((Box 2 K).filter (fun u => ∑ i, u i = 3)).card * cf n ξ ε (j + 1) (l + 3) 3) := by
            gcongr
        _ = (((Box 2 K).filter (fun u => ∑ i, u i = 3)).card : ℝ) *
            (((1 : ℝ) / 2) ^ 3 * cf n ξ ε (j + 1) (l + 3) 3 *
              Vt n K ξ ε (m' / 2) (j + 1) (l + 3)) := by ring
    · -- pairs with `b ≠ 3`: trivial bound, `cf = 1`
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u hu => ?_))
      have hb : ¬ (∑ i, u i = 3) := (Finset.mem_filter.1 hu).2
      have hcf : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) = 1 := by
        unfold cf; rw [if_neg (fun h => hb h.1)]
      rw [hcf, mul_one, norm_mul, norm_mul, AddChar.norm_apply, mul_one, norm_pow, norm_div,
        norm_one, Complex.norm_two]
      gcongr
      exact IH _

theorem norm_chi_le_Vt (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖chi n K ξ‖ ≤ Vt n K ξ ε (n / 2) 0 0 := by
  have h := norm_Phi_le_Vt n K ξ ε hε hε1 n 0 0
  simp only [pow_zero, mul_one] at h
  rw [chi_eq_Phi]
  exact h

/-- Tao Proposition 7.3 (renewal process meets many white points), finite truncated form. -/
def Prop73 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K →
    ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → Vt n K ξ ε (n / 2) 0 0 ≤ C * (n : ℝ) ^ (-A)

theorem prop117_of_73 (h : Prop73) : Prop117 := by
  obtain ⟨ε, hε, hε1, hA⟩ := h
  intro A hA0
  obtain ⟨C, hC, hb⟩ := hA A hA0
  exact ⟨C, hC, fun n K hn hK ξ hξ => (norm_chi_le_Vt n K ξ ε hε hε1).trans (hb n K hn hK ξ hξ)⟩


lemma ps_eq_sum (a : ℕ → ℕ) (k : ℕ) : ps a k = ∑ i ∈ Finset.range k, a i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- The recursion (7.35) satisfied by `V`, def-free (abstracts `Vt`). -/
def VRec (n K : ℕ) (ξ : ℤ) (ε : ℝ) (V : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ j l : ℕ, V 0 j l = 1) ∧ ∀ r j l : ℕ, V (r + 1) j l =
    ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
      (if (∑ i, u i) = 3 ∧
          ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
            ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
          ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
            ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
        then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)

theorem Vt_rec (n K : ℕ) (ξ : ℤ) (ε : ℝ) : VRec n K ξ ε (Vt n K ξ ε) := by
  refine ⟨fun j l => rfl, fun r j l => Finset.sum_congr rfl fun u _ => ?_⟩
  exact congrArg (· * Vt n K ξ ε r (j + 1) (l + ∑ i, u i))
    (congrArg (((1 : ℝ) / 2) ^ (∑ i, u i) * ·) (by
      unfold cf White thZ
      split_ifs with h1 h2 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1)))

theorem eq_Vt_of_rec (n K : ℕ) (ξ : ℤ) (ε : ℝ) (V : ℕ → ℕ → ℕ → ℝ) (h : VRec n K ξ ε V) :
    ∀ r j l, V r j l = Vt n K ξ ε r j l := by
  intro r
  induction r with
  | zero => intro j l; rw [h.1]; rfl
  | succ r ih =>
    intro j l
    rw [h.2, (Vt_rec n K ξ ε).2]
    simp only [ih]


theorem chi_eq_inl (n K : ℕ) (ξ : ℤ) : chi n K ξ =
    ∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n) := by
  simp only [chi, syrZ, Fnat, ps_eq_sum, padv, Box]

end Tao31

open Tao31 in
theorem solution :
    ∀ n K : ℕ, ∀ ξ : ℤ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ V (n / 2) 0 0 := by
  intro n K ξ ε hε hε1 V h0 h1
  rw [← Tao31.chi_eq_inl, Tao31.eq_Vt_of_rec n K ξ ε V ⟨h0, h1⟩]
  exact Tao31.norm_chi_le_Vt n K ξ ε hε hε1
