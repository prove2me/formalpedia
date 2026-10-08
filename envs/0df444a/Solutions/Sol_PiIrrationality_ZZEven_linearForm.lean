-- Prove2me | solution 1 for PiIrrationality.ZZEven.linearForm
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:03:02.538703+00:00
-- url     : https://prove2.me/submissions/4be299b1-65e6-4f64-89fc-a11481b8322b

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Zeilberger–Zudilin even linear forms: `M_n J_n = U_n + V_n π`

Self-contained proof of `PiIrrationality.ZZEven.linearForm` (Bai, arXiv:2609.11276,
Proposition 2.7 with exponents (2, 4, 6)).
-/

/-! ## Module `Psi` -/

section
open PowerSeries Polynomial

namespace PiIrrationality.ZZEven.Arith

/-- `B(w) = (2w-1)^{4n} (5w^2-4w+1)^{4n} (5w^2-6w+2)^{4n}`. -/
noncomputable def Bp (n : ℕ) : ℤ[X] :=
  (2 * Polynomial.X - 1) ^ (4 * n) * (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (4 * n) *
    (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2) ^ (4 * n)

/-- The negative binomial series `(1-w)^{-(d+1)} = Σ C(d+m, d) w^m`. -/
noncomputable def G (d : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun m => (Nat.choose (d + m) d : ℤ)

lemma G_mul (d : ℕ) : G d * (1 - PowerSeries.X) ^ (d + 1) = 1 :=
  mk_add_choose_mul_one_sub_pow_eq_one (S := ℤ) (d := d)

/-- `Ψ(w) = B(w) (1-w)^{-6n-1}`. -/
noncomputable def Psi (n : ℕ) : ℤ⟦X⟧ := (Bp n : ℤ⟦X⟧) * G (6 * n)

/-- `ψ_m = [w^m] Ψ(w)`. -/
noncomputable def psi (n m : ℕ) : ℤ := PowerSeries.coeff m (Psi n)

/-! ### `ψ_{6n} = coef_n` -/

/-- `u = (1-w)^{-1}`. -/
noncomputable def u : ℤ⟦X⟧ := G 0

lemma u_mul : u * (1 - PowerSeries.X) = 1 := by
  have := G_mul 0
  simpa [u] using this

lemma G_eq_u_pow (d : ℕ) : G d = u ^ (d + 1) := by
  have h1 := G_mul d
  have h2 : u ^ (d + 1) * (1 - PowerSeries.X) ^ (d + 1) = 1 := by rw [← mul_pow, u_mul, one_pow]
  calc G d = G d * (u ^ (d + 1) * (1 - PowerSeries.X) ^ (d + 1)) := by rw [h2, mul_one]
    _ = (G d * (1 - PowerSeries.X) ^ (d + 1)) * u ^ (d + 1) := by ring
    _ = u ^ (d + 1) := by rw [h1, one_mul]

/-- `ζ = -w/(1-w)`. -/
noncomputable def ζ : ℤ⟦X⟧ := -PowerSeries.X * u

lemma ζ_mul : ζ * (1 - PowerSeries.X) = -PowerSeries.X := by
  rw [ζ, mul_assoc, u_mul, mul_one]

lemma coeff_one_sub_X_pow (m k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.X : ℤ⟦X⟧) ^ m) = (-1) ^ k * (m.choose k : ℤ) := by
  have : (1 - PowerSeries.X : ℤ⟦X⟧) ^ m = (((1 - Polynomial.X : ℤ[X]) ^ m : ℤ[X]) : ℤ⟦X⟧) := by
    push_cast; rfl
  rw [this, Polynomial.coeff_coe]
  have h2 : (1 - Polynomial.X : ℤ[X]) = (-1 : ℤ[X]) * (Polynomial.X + Polynomial.C (-1)) := by
    simp [Polynomial.C_neg]; ring
  rw [h2, mul_pow, ← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rcases le_or_gt k m with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    have hd : ((-1 : ℤ) ^ d) ^ 2 = 1 := by
      rw [← pow_mul]; exact Even.neg_one_pow ⟨d, by ring⟩
    calc (-1 : ℤ) ^ (k + d) * ((-1) ^ d * ((k + d).choose k : ℤ))
        = (-1) ^ k * ((-1) ^ d) ^ 2 * ((k + d).choose k : ℤ) := by ring
      _ = (-1) ^ k * ((k + d).choose k : ℤ) := by rw [hd, mul_one]
  · simp [Nat.choose_eq_zero_of_lt h]

set_option maxHeartbeats 1000000 in
/-- The base identity `A(ζ) (1-w)^{20} = B_1(w)`. -/
lemma A_eval_base :
    (A.eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ) * (1 - PowerSeries.X) ^ 20 =
      ((2 * PowerSeries.X - 1) ^ 4 * (5 * PowerSeries.X ^ 2 - 4 * PowerSeries.X + 1) ^ 4 *
        (5 * PowerSeries.X ^ 2 - 6 * PowerSeries.X + 2) ^ 4 : ℤ⟦X⟧) := by
  set y : ℤ⟦X⟧ := 1 - PowerSeries.X with hy
  have hζ : ζ * y = -PowerSeries.X := ζ_mul
  have hA : A.eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ =
      (1 + ζ) ^ 4 * ((2 : ℤ⟦X⟧) + 6 * ζ + 9 * ζ ^ 2 + 6 * ζ ^ 3 + 2 * ζ ^ 4) ^ 4 := by
    simp only [A, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_add,
      Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_C]
    norm_num
  rw [hA]
  have e1 : (1 + ζ) ^ 4 * y ^ 4 = (y + ζ * y) ^ 4 := by ring
  have e2 : ((2 : ℤ⟦X⟧) + 6 * ζ + 9 * ζ ^ 2 + 6 * ζ ^ 3 + 2 * ζ ^ 4) * y ^ 4 =
      2 * y ^ 4 + 6 * (ζ * y) * y ^ 3 + 9 * (ζ * y) ^ 2 * y ^ 2 + 6 * (ζ * y) ^ 3 * y +
        2 * (ζ * y) ^ 4 := by ring
  calc (1 + ζ) ^ 4 * ((2 : ℤ⟦X⟧) + 6 * ζ + 9 * ζ ^ 2 + 6 * ζ ^ 3 + 2 * ζ ^ 4) ^ 4 * y ^ 20
      = ((1 + ζ) ^ 4 * y ^ 4) * (((2 : ℤ⟦X⟧) + 6 * ζ + 9 * ζ ^ 2 + 6 * ζ ^ 3 + 2 * ζ ^ 4) *
          y ^ 4) ^ 4 := by ring
    _ = _ := by
      rw [e1, e2, hζ, hy]
      ring


lemma coe_ofNat' (m : ℕ) [m.AtLeastTwo] :
    ((OfNat.ofNat m : ℤ[X]) : ℤ⟦X⟧) = (OfNat.ofNat m : ℤ⟦X⟧) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]

lemma Bp_coe (n : ℕ) : (Bp n : ℤ⟦X⟧) =
    ((2 * PowerSeries.X - 1) ^ 4 * (5 * PowerSeries.X ^ 2 - 4 * PowerSeries.X + 1) ^ 4 *
      (5 * PowerSeries.X ^ 2 - 6 * PowerSeries.X + 2) ^ 4 : ℤ⟦X⟧) ^ n := by
  simp only [Bp, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_add,
    Polynomial.coe_X, Polynomial.coe_one]
  have h2 : (((2 : ℤ[X])) : ℤ⟦X⟧) = 2 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
  have h4 : (((4 : ℤ[X])) : ℤ⟦X⟧) = 4 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
  have h5 : (((5 : ℤ[X])) : ℤ⟦X⟧) = 5 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
  have h6 : (((6 : ℤ[X])) : ℤ⟦X⟧) = 6 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
  rw [h2, h4, h5, h6, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm 4 n]

lemma Bp_eq_eval (n : ℕ) : (Bp n : ℤ⟦X⟧) =
    (A ^ n).eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ * (1 - PowerSeries.X) ^ (20 * n) := by
  rw [Polynomial.eval₂_pow, pow_mul, ← mul_pow, A_eval_base, Bp_coe]

lemma Psi_eq (n : ℕ) (hn : 1 ≤ n) : Psi n =
    (A ^ n).eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ * (1 - PowerSeries.X) ^ (14 * n - 1) := by
  rw [Psi, Bp_eq_eval, G_eq_u_pow]
  have h : (1 - PowerSeries.X : ℤ⟦X⟧) ^ (20 * n) = (1 - PowerSeries.X) ^ (14 * n - 1) *
      (1 - PowerSeries.X) ^ (6 * n + 1) := by rw [← pow_add]; congr 1; omega
  rw [h]
  have hu : u ^ (6 * n + 1) * (1 - PowerSeries.X) ^ (6 * n + 1) = 1 := by rw [← mul_pow, u_mul, one_pow]
  calc (A ^ n).eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ *
        ((1 - PowerSeries.X) ^ (14 * n - 1) * (1 - PowerSeries.X) ^ (6 * n + 1)) * u ^ (6 * n + 1)
      = (A ^ n).eval₂ (Nat.castRingHom ℤ⟦X⟧) ζ * (1 - PowerSeries.X) ^ (14 * n - 1) *
          (u ^ (6 * n + 1) * (1 - PowerSeries.X) ^ (6 * n + 1)) := by ring
    _ = _ := by rw [hu, mul_one]

/-- The coefficient of `X^m` in `(-X)^k u^k (1-X)^e` for `k ≤ m`, `k ≤ e`. -/
lemma coeff_term (k e m : ℕ) (hk : k ≤ e) :
    PowerSeries.coeff m ((-PowerSeries.X) ^ k * u ^ k * (1 - PowerSeries.X : ℤ⟦X⟧) ^ e) =
      if k ≤ m then (-1) ^ m * ((e - k).choose (m - k) : ℤ) else 0 := by
  have h1 : u ^ k * (1 - PowerSeries.X : ℤ⟦X⟧) ^ e = (1 - PowerSeries.X) ^ (e - k) := by
    rw [show e = k + (e - k) by omega, pow_add, ← mul_assoc, ← mul_pow, u_mul, one_pow, one_mul]
    congr 1; omega
  have hc : (-1 : ℤ⟦X⟧) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) := by simp
  rw [mul_assoc, h1, neg_pow, hc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with hkm
  · rw [coeff_one_sub_X_pow]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
    rw [Nat.add_sub_cancel_left, pow_add]; ring
  · simp


/-- **`ψ_{6n} = coef_n`**: the residue identity behind the positive coefficient. -/
theorem psi_six_mul_eq_coef (n : ℕ) (hn : 1 ≤ n) : psi n (6 * n) = (coef n : ℤ) := by
  unfold psi coef
  rw [Psi_eq n hn]
  set N := (A ^ n).natDegree + 6 * n + 1 with hN
  rw [Polynomial.eval₂_eq_sum_range' (Nat.castRingHom ℤ⟦X⟧) (n := N) (by omega)]
  rw [Finset.sum_mul, map_sum]
  have hterm : ∀ k ∈ Finset.range N,
      PowerSeries.coeff (6 * n) ((Nat.castRingHom ℤ⟦X⟧) ((A ^ n).coeff k) * ζ ^ k *
        (1 - PowerSeries.X) ^ (14 * n - 1)) =
      if k ≤ 6 * n then ((A ^ n).coeff k : ℤ) * ((14 * n - 1 - k).choose (6 * n - k) : ℤ) else 0 := by
    intro k _
    have hcast : (Nat.castRingHom ℤ⟦X⟧) ((A ^ n).coeff k) = PowerSeries.C (((A ^ n).coeff k : ℤ)) := by
      simp
    rw [hcast, ζ, mul_pow, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, ← mul_assoc]
    by_cases hk : k ≤ 6 * n
    · rw [coeff_term k (14 * n - 1) (6 * n) (by omega), if_pos hk, if_pos hk]
      rw [show (-1 : ℤ) ^ (6 * n) = 1 by rw [pow_mul]; norm_num]; ring
    · rw [if_neg hk]
      have : PowerSeries.coeff (6 * n) ((-PowerSeries.X) ^ k * u ^ k *
          (1 - PowerSeries.X : ℤ⟦X⟧) ^ (14 * n - 1)) = 0 := by
        rw [neg_pow, mul_assoc, mul_assoc]
        have hc : (-1 : ℤ⟦X⟧) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) := by simp
        rw [hc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg hk, mul_zero]
      rw [this, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfilt : (Finset.range N).filter (fun k => k ≤ 6 * n) = Finset.range (6 * n + 1) := by
    ext k; simp [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show 14 * n - 1 - k = 8 * n - 1 + (6 * n - k) by omega]


/-! ### The 2-adic valuation of `ψ_m` -/

/-- The polynomial without its `2`-heavy factor. -/
noncomputable def W (n c : ℕ) : ℤ[X] :=
  (2 * Polynomial.X - 1) ^ (4 * n) * (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (4 * n) *
    (((4 * n).choose c : ℤ[X]) * 5 ^ c * (1 - 3 * Polynomial.X) ^ (4 * n - c))

lemma Bp_sum (n : ℕ) : Bp n = ∑ c ∈ Finset.range (4 * n + 1),
    (2 : ℤ[X]) ^ (4 * n - c) * Polynomial.X ^ (2 * c) * W n c := by
  have h : (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2 : ℤ[X]) =
      5 * Polynomial.X ^ 2 + 2 * (1 - 3 * Polynomial.X) := by ring
  rw [Bp, h, add_pow (5 * Polynomial.X ^ 2) (2 * (1 - 3 * Polynomial.X)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold W
  rw [mul_pow, mul_pow (2 : ℤ[X]), ← pow_mul]
  ring

/-- `2^{4n - ⌊m/2⌋}` divides `ψ_m`. -/
theorem psi_two_adic (n m : ℕ) : (2 : ℤ) ^ (4 * n - m / 2) ∣ psi n m := by
  unfold psi Psi
  rw [Bp_sum, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.sum_mul, map_sum]
  apply Finset.dvd_sum
  intro c hc
  rw [Finset.mem_range] at hc
  have e : Polynomial.coeToPowerSeries.ringHom
      ((2 : ℤ[X]) ^ (4 * n - c) * Polynomial.X ^ (2 * c) * W n c) * G (6 * n) =
      PowerSeries.C ((2 : ℤ) ^ (4 * n - c)) * (PowerSeries.X ^ (2 * c) * ((W n c : ℤ⟦X⟧) * G (6 * n))) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_ofNat, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    simp only [map_pow, map_ofNat]; ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · apply Dvd.dvd.mul_right
    apply pow_dvd_pow
    omega
  · simp

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Prime` -/

section
open PowerSeries Polynomial

namespace PiIrrationality.ZZEven.Arith

variable {F : Type*} [Field F]

/-- A polynomial whose coefficients vanish at every `r` with `r + 1 = 0` has an antiderivative. -/
lemma exists_antideriv (f : F[X]) (h : ∀ r : ℕ, ((r : F) + 1) = 0 → f.coeff r = 0) :
    ∃ V : F[X], Polynomial.derivative V = f := by
  refine ⟨∑ r ∈ Finset.range (f.natDegree + 1),
    Polynomial.C (f.coeff r * ((r : F) + 1)⁻¹) * Polynomial.X ^ (r + 1), ?_⟩
  ext r
  rw [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single r]
  · simp only
    by_cases hr : r ∈ Finset.range (f.natDegree + 1)
    · by_cases h0 : ((r : F) + 1) = 0
      · rw [h r h0]; simp
      · push_cast; field_simp
    · rw [Finset.mem_range, not_lt] at hr
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · intro b _ hb
    rw [if_neg (by omega)]
  · intro hr
    rw [if_pos rfl]
    rw [Finset.mem_range, not_lt] at hr
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp


/-- `h(y) = y^A (25y^2+6y+1)^B (1-y)^e`. -/
noncomputable def hpoly (A B e : ℕ) : F[X] :=
  Polynomial.X ^ A * ((25 * Polynomial.X ^ 2 + 6 * Polynomial.X + 1) ^ B * (1 - Polynomial.X) ^ e)

lemma hpoly_coeff_zero (A B e ρ : ℕ) (h : ρ < A ∨ A + (2 * B + e) < ρ) :
    (hpoly (F := F) A B e).coeff ρ = 0 := by
  unfold hpoly
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hA
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h1 : ((25 * Polynomial.X ^ 2 + 6 * Polynomial.X + 1 : F[X]) ^ B).natDegree ≤ 2 * B := by
      apply le_trans (Polynomial.natDegree_pow_le) (Nat.mul_le_mul_left _ _) |>.trans (le_of_eq (mul_comm _ _))
      compute_degree!
    have h2 : ((1 - Polynomial.X : F[X]) ^ e).natDegree ≤ e := by
      apply le_trans (Polynomial.natDegree_pow_le)
      have : (1 - Polynomial.X : F[X]).natDegree ≤ 1 := by compute_degree!
      nlinarith
    have h3 := Polynomial.natDegree_mul_le (p := (25 * Polynomial.X ^ 2 + 6 * Polynomial.X + 1 : F[X]) ^ B)
      (q := (1 - Polynomial.X : F[X]) ^ e)
    omega
  · rfl


section ZModP

variable (p : ℕ) [hp : Fact p.Prime]

/-- `H_s(s) = κ · h(s^2)` in characteristic `p`. -/
noncomputable def Hs (A B e : ℕ) : (ZMod p)[X] :=
  Polynomial.C (((16 : ZMod p)⁻¹) ^ B * ((4 : ZMod p)⁻¹) ^ e) * Polynomial.expand (ZMod p) 2 (hpoly A B e)

/-- The support condition gives an antiderivative of `H_s`. -/
lemma Hs_antideriv (A B e : ℕ)
    (hsupp : ∀ ρ : ℕ, A ≤ ρ → ρ ≤ A + (2 * B + e) → ¬ p ∣ 2 * ρ + 1) :
    ∃ V : (ZMod p)[X], Polynomial.derivative V = Hs p A B e := by
  apply exists_antideriv
  intro r hr
  have hpr : p ∣ r + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact hr
  unfold Hs
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_expand (by norm_num)]
  split_ifs with h2
  · obtain ⟨ρ, rfl⟩ := h2
    rw [show 2 * ρ / 2 = ρ by omega, hpoly_coeff_zero, mul_zero]
    by_contra hcon
    push Not at hcon
    exact hsupp ρ hcon.1 hcon.2 hpr
  · simp


lemma two_ne_zero_zmod (hp5 : 5 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- `E(w) = (5w^2-4w+1)(5w^2-6w+2)`. -/
noncomputable def Ew : (ZMod p)[X] :=
  (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) * (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2)

/-- `H_w(w) = (2w-1)^{2A} E(w)^B (w(1-w))^e`. -/
noncomputable def Hw (A B e : ℕ) : (ZMod p)[X] :=
  (2 * Polynomial.X - 1) ^ (2 * A) * Ew p ^ B * (Polynomial.X * (1 - Polynomial.X)) ^ e

lemma Hs_comp (hp5 : 5 < p) (A B e : ℕ) :
    (Hs p A B e).comp (2 * Polynomial.X - 1) = Hw p A B e := by
  have h2 := two_ne_zero_zmod p hp5
  have h16 : (16 : ZMod p) * 16⁻¹ = 1 := mul_inv_cancel₀ (by
    rw [show (16 : ZMod p) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2)
  have h4 : (4 : ZMod p) * 4⁻¹ = 1 := mul_inv_cancel₀ (by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2)
  unfold Hs Hw hpoly Ew
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.expand_eq_comp_X_pow,
    Polynomial.comp_assoc]
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.one_comp, Polynomial.ofNat_comp]
  push_cast
  have e1 : (25 * ((2 * Polynomial.X - 1) ^ 2) ^ 2 + 6 * (2 * Polynomial.X - 1) ^ 2 + 1 : (ZMod p)[X]) =
      Polynomial.C 16 * ((5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) *
        (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2)) := by
    rw [show (Polynomial.C 16 : (ZMod p)[X]) = 16 by simp [map_ofNat]]; ring
  have e2 : (1 - (2 * Polynomial.X - 1) ^ 2 : (ZMod p)[X]) =
      Polynomial.C 4 * (Polynomial.X * (1 - Polynomial.X)) := by
    rw [show (Polynomial.C 4 : (ZMod p)[X]) = 4 by simp [map_ofNat]]; ring
  rw [e1, e2, ← pow_mul, mul_pow (Polynomial.C (16 : ZMod p)), mul_pow (Polynomial.C (4 : ZMod p)),
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_pow]
  have k16 : (Polynomial.C (16 : ZMod p)⁻¹) ^ B * (Polynomial.C 16) ^ B = 1 := by
    rw [← mul_pow, ← Polynomial.C_mul, mul_comm, h16, Polynomial.C_1, one_pow]
  have k4 : (Polynomial.C (4 : ZMod p)⁻¹) ^ e * (Polynomial.C 4) ^ e = 1 := by
    rw [← mul_pow, ← Polynomial.C_mul, mul_comm, h4, Polynomial.C_1, one_pow]
  calc _ = ((Polynomial.C (16 : ZMod p)⁻¹) ^ B * (Polynomial.C 16) ^ B) *
        ((Polynomial.C (4 : ZMod p)⁻¹) ^ e * (Polynomial.C 4) ^ e) *
        ((2 * Polynomial.X - 1) ^ (2 * A) *
          ((5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) * (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2)) ^ B *
          (Polynomial.X * (1 - Polynomial.X)) ^ e) := by ring
    _ = _ := by rw [k16, k4, one_mul, one_mul]

/-- `H_w` has an antiderivative. -/
lemma Hw_antideriv (hp5 : 5 < p) (A B e : ℕ)
    (hsupp : ∀ ρ : ℕ, A ≤ ρ → ρ ≤ A + (2 * B + e) → ¬ p ∣ 2 * ρ + 1) :
    ∃ V : (ZMod p)[X], Polynomial.derivative V = Hw p A B e := by
  obtain ⟨V, hV⟩ := Hs_antideriv p A B e hsupp
  have h2 := two_ne_zero_zmod p hp5
  refine ⟨Polynomial.C (2 : ZMod p)⁻¹ * V.comp (2 * Polynomial.X - 1), ?_⟩
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_comp, hV, ← Hs_comp p hp5]
  have hd : Polynomial.derivative (2 * Polynomial.X - 1 : (ZMod p)[X]) = Polynomial.C 2 := by
    simp [map_ofNat]
  rw [hd, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ h2, Polynomial.C_1, one_mul]


/-- The map of `G d` to characteristic `p`. -/
noncomputable def Gp (d : ℕ) : (ZMod p)⟦X⟧ := PowerSeries.mk fun m => ((Nat.choose (d + m) d : ℕ) : ZMod p)

lemma map_G (d : ℕ) : PowerSeries.map (Int.castRingHom (ZMod p)) (G d) = Gp p d := by
  ext m; simp [G, Gp, PowerSeries.coeff_map]

lemma Gp_mul (d : ℕ) : Gp p d * (1 - PowerSeries.X) ^ (d + 1) = 1 :=
  mk_add_choose_mul_one_sub_pow_eq_one (S := ZMod p) (d := d)

/-- `uP = (1-w)^{-1}` in characteristic `p`. -/
noncomputable def uP : (ZMod p)⟦X⟧ := Gp p 0

lemma uP_mul : uP p * (1 - PowerSeries.X) = 1 := by
  have := Gp_mul p 0; simpa [uP] using this

lemma Gp_eq (d : ℕ) : Gp p d = uP p ^ (d + 1) := by
  have h1 := Gp_mul p d
  have h2 : uP p ^ (d + 1) * (1 - PowerSeries.X) ^ (d + 1) = 1 := by rw [← mul_pow, uP_mul, one_pow]
  calc Gp p d = Gp p d * (uP p ^ (d + 1) * (1 - PowerSeries.X) ^ (d + 1)) := by rw [h2, mul_one]
    _ = (Gp p d * (1 - PowerSeries.X) ^ (d + 1)) * uP p ^ (d + 1) := by ring
    _ = uP p ^ (d + 1) := by rw [h1, one_mul]

lemma map_coe_poly (f : ℤ[X]) :
    PowerSeries.map (Int.castRingHom (ZMod p)) (f : ℤ⟦X⟧) =
      ((f.map (Int.castRingHom (ZMod p)) : (ZMod p)[X]) : (ZMod p)⟦X⟧) := by
  ext m; simp [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_map]

/-- The reduction of `B` modulo `p`. -/
lemma Bp_map (n : ℕ) : (Bp n).map (Int.castRingHom (ZMod p)) =
    (2 * Polynomial.X - 1) ^ (4 * n) * Ew p ^ (4 * n) := by
  simp [Bp, Ew, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    mul_pow, map_ofNat]
  ring

/-- **Prime deletion** (Bai, Lemma 2.2) in terms of `ψ`. -/
theorem psi_prime_dvd (n : ℕ) (hp5 : 5 < p) (A B C qa qb qc : ℕ)
    (hA : 2 * n = qa * p + A) (hB : 4 * n = qb * p + B) (hC : 6 * n = qc * p + C)
    (hCp : C < p)
    (hsupp : ∀ ρ : ℕ, A ≤ ρ → ρ ≤ A + (2 * B + (p - 1 - C)) → ¬ p ∣ 2 * ρ + 1)
    (m : ℕ) (hm : m % p = C) : (p : ℤ) ∣ psi n m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set e := p - 1 - C with he
  obtain ⟨V, hV⟩ := Hw_antideriv p hp5 A B e hsupp
  -- the reduced series
  have hΨ : PowerSeries.map (Int.castRingHom (ZMod p)) (Psi n) =
      ((((2 * Polynomial.X - 1) ^ (4 * n) * Ew p ^ (4 * n) : (ZMod p)[X])) : (ZMod p)⟦X⟧) *
        uP p ^ (6 * n + 1) := by
    rw [Psi, map_mul, map_coe_poly, Bp_map, map_G, Gp_eq]
  -- T := S · u^{qc+1}
  set S : (ZMod p)[X] := (2 * Polynomial.X - 1) ^ (2 * qa) * Ew p ^ qb with hS
  set T : (ZMod p)⟦X⟧ := (S : (ZMod p)⟦X⟧) * uP p ^ (qc + 1) with hT
  have hKe : (qc + 1) * p = 6 * n + 1 + e := by
    have : C ≤ p - 1 := by omega
    rw [he]; zify [this, Nat.one_le_of_lt hCp] at *; push_cast at *; nlinarith
  -- X^e Ψ̄ = T^p H_w
  have hkey : (PowerSeries.X : (ZMod p)⟦X⟧) ^ e * PowerSeries.map (Int.castRingHom (ZMod p)) (Psi n) =
      T ^ p * ((Hw p A B e : (ZMod p)[X]) : (ZMod p)⟦X⟧) := by
    have hpoly : (S ^ p * Hw p A B e : (ZMod p)[X]) =
        (2 * Polynomial.X - 1) ^ (4 * n) * Ew p ^ (4 * n) * Polynomial.X ^ e * (1 - Polynomial.X) ^ e := by
      have e1 : (2 * Polynomial.X - 1 : (ZMod p)[X]) ^ (4 * n) =
          (2 * Polynomial.X - 1) ^ (2 * qa * p) * (2 * Polynomial.X - 1) ^ (2 * A) := by
        rw [← pow_add]; congr 1; linarith
      have e2 : Ew p ^ (4 * n) = Ew p ^ (qb * p) * Ew p ^ B := by
        rw [← pow_add, hB]
      rw [hS, Hw, e1, e2, mul_pow, ← pow_mul, ← pow_mul, mul_pow Polynomial.X]
      try ring
    rw [hΨ, hT, mul_pow, ← pow_mul]
    have hu : uP p ^ ((qc + 1) * p) = uP p ^ (6 * n + 1) * uP p ^ e := by rw [hKe, pow_add]
    have hue : uP p ^ e * (1 - PowerSeries.X) ^ e = 1 := by rw [← mul_pow, uP_mul, one_pow]
    have hcoe : ((S : (ZMod p)⟦X⟧) ^ p * ((Hw p A B e : (ZMod p)[X]) : (ZMod p)⟦X⟧)) =
        (((2 * Polynomial.X - 1) ^ (4 * n) * Ew p ^ (4 * n) : (ZMod p)[X]) : (ZMod p)⟦X⟧) *
          PowerSeries.X ^ e * (1 - PowerSeries.X) ^ e := by
      rw [← Polynomial.coe_pow, ← Polynomial.coe_mul, hpoly]; push_cast; rfl
    rw [hu, show (S : (ZMod p)⟦X⟧) ^ p * (uP p ^ (6 * n + 1) * uP p ^ e) *
        ((Hw p A B e : (ZMod p)[X]) : (ZMod p)⟦X⟧) =
        ((S : (ZMod p)⟦X⟧) ^ p * ((Hw p A B e : (ZMod p)[X]) : (ZMod p)⟦X⟧)) *
          (uP p ^ (6 * n + 1) * uP p ^ e) by ring, hcoe]
    linear_combination (-(PowerSeries.X ^ e *
      ((((2 * Polynomial.X - 1) ^ (4 * n) * Ew p ^ (4 * n) : (ZMod p)[X])) : (ZMod p)⟦X⟧) *
        uP p ^ (6 * n + 1))) * hue
  -- Y := T^p V, with Y' = T^p H_w
  set Y : (ZMod p)⟦X⟧ := T ^ p * ((V : (ZMod p)[X]) : (ZMod p)⟦X⟧) with hY
  have hderiv : PowerSeries.derivative (ZMod p) Y = T ^ p * ((Hw p A B e : (ZMod p)[X]) : (ZMod p)⟦X⟧) := by
    rw [hY, Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_coe, hV]
    have hp0 : ((p : ℕ) : (ZMod p)⟦X⟧) = 0 := by
      rw [← map_natCast (PowerSeries.C (R := ZMod p)), ZMod.natCast_self, map_zero]
    rw [hp0]; simp
  -- coefficient comparison
  have h1 : PowerSeries.coeff (m + e) ((PowerSeries.X : (ZMod p)⟦X⟧) ^ e *
      PowerSeries.map (Int.castRingHom (ZMod p)) (Psi n)) = ((psi n m : ℤ) : ZMod p) := by
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, PowerSeries.coeff_map]
    rfl
  rw [← h1, hkey, ← hderiv, PowerSeries.coeff_derivative]
  have hzero : ((m + e : ℕ) : ZMod p) + 1 = 0 := by
    have : p ∣ m + e + 1 := by
      have hmC : m = p * (m / p) + C := by rw [← hm]; exact (Nat.div_add_mod m p).symm
      refine ⟨m / p + 1, ?_⟩
      rw [he, Nat.mul_add, Nat.mul_one]; omega
    rw [← ZMod.natCast_eq_zero_iff] at this; push_cast at this ⊢; exact this
  rw [hzero, mul_zero]

end ZModP

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Deleted` -/

section
open PowerSeries Polynomial

namespace PiIrrationality.ZZEven.Arith

/-- The defining inequality of a deleted prime, in natural numbers. -/
lemma deleted_ineq {n p : ℕ} (hp : p ∈ deletedPrimes n) :
    (4 * n + p) % (2 * p) + 4 * (4 * n % p) < 2 * (6 * n % p) := by
  unfold deletedPrimes at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hpr, _, _, hfr⟩ := hp
  have hp0 : 0 < p := hpr.pos
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp0
  have hx : (2 * n : ℚ) / p + 1 / 2 = ((4 * n + p : ℕ) : ℚ) / ((2 * p : ℕ) : ℚ) := by
    push_cast; field_simp; ring
  have h4 : (4 * n : ℚ) / p = ((4 * n : ℕ) : ℚ) / ((p : ℕ) : ℚ) := by push_cast; rfl
  have h6 : (6 * n : ℚ) / p = ((6 * n : ℕ) : ℚ) / ((p : ℕ) : ℚ) := by push_cast; rfl
  rw [hx, h4, h6, Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod] at hfr
  have key : (((4 * n + p) % (2 * p) : ℕ) : ℚ) + 4 * ((4 * n % p : ℕ) : ℚ) < 2 * ((6 * n % p : ℕ) : ℚ) := by
    have h2p : (0 : ℚ) < ((2 * p : ℕ) : ℚ) := by positivity
    have := mul_lt_mul_of_pos_right hfr h2p
    push_cast at this ⊢
    field_simp at this
    linarith
  exact_mod_cast key

/-- The remainder `(4n+p) mod 2p` in terms of `A = 2n mod p`. -/
lemma mod_two_p (n p : ℕ) (hp : 0 < p) :
    (4 * n + p) % (2 * p) =
      if 2 * (2 * n % p) < p then 2 * (2 * n % p) + p else 2 * (2 * n % p) - p := by
  have hA : 2 * n % p < p := Nat.mod_lt _ hp
  have h4 : 4 * n + p = (2 * n / p) * (2 * p) + (2 * (2 * n % p) + p) := by
    have := Nat.div_add_mod (2 * n) p
    nlinarith
  rw [h4, Nat.mul_add_mod_self_right]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The support condition needed for prime deletion. -/
lemma deleted_supp {n p : ℕ} (hp : p ∈ deletedPrimes n) :
    ∀ ρ : ℕ, 2 * n % p ≤ ρ → ρ ≤ 2 * n % p + (2 * (4 * n % p) + (p - 1 - 6 * n % p)) →
      ¬ p ∣ 2 * ρ + 1 := by
  have hineq := deleted_ineq hp
  unfold deletedPrimes at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hpr, h5, _, _⟩ := hp
  have hp0 : 0 < p := hpr.pos
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2 : 2 ∣ p := by omega
    rcases hpr.eq_one_or_self_of_dvd 2 h2 with h' | h' <;> omega
  rw [mod_two_p n p hp0] at hineq
  have hA : 2 * n % p < p := Nat.mod_lt _ hp0
  have hB : 4 * n % p < p := Nat.mod_lt _ hp0
  have hC : 6 * n % p < p := Nat.mod_lt _ hp0
  intro ρ hlo hhi hdvd
  obtain ⟨t, ht⟩ := hdvd
  split_ifs at hineq with h
  · -- 2ρ+1 < p
    have : 2 * ρ + 1 < p := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; omega
    · have : p ≤ p * t := Nat.le_mul_of_pos_right p h0
      omega
  · -- p < 2ρ+1 < 3p forces 2ρ+1 = 2p
    have hlow : p < 2 * ρ + 1 := by omega
    have hhigh : 2 * ρ + 1 < 3 * p := by omega
    rw [ht] at hlow hhigh
    have t1 : 1 < t := by
      by_contra hc; push Not at hc
      have : p * t ≤ p * 1 := Nat.mul_le_mul_left p hc
      omega
    have t3 : t < 3 := by
      by_contra hc; push Not at hc
      have : p * 3 ≤ p * t := Nat.mul_le_mul_left p hc
      omega
    have : t = 2 := by omega
    subst this
    omega

/-- Prime deletion for every deleted prime. -/
theorem psi_deleted_dvd {n p : ℕ} (hp : p ∈ deletedPrimes n) (m : ℕ) (hm : m % p = 6 * n % p) :
    (p : ℤ) ∣ psi n m := by
  have hsupp := deleted_supp hp
  unfold deletedPrimes at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hpr, h5, _, _⟩ := hp
  have : Fact p.Prime := ⟨hpr⟩
  exact psi_prime_dvd p n h5 (2 * n % p) (4 * n % p) (6 * n % p) (2 * n / p) (4 * n / p) (6 * n / p)
    (by have := Nat.div_add_mod (2 * n) p; linarith) (by have := Nat.div_add_mod (4 * n) p; linarith)
    (by have := Nat.div_add_mod (6 * n) p; linarith) (Nat.mod_lt _ hpr.pos) hsupp m hm

end PiIrrationality.ZZEven.Arith

namespace PiIrrationality.ZZEven.Arith

/-- A product of distinct primes divides every integer that each of them divides. -/
lemma primes_prod_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (z : ℤ)
    (h : ∀ p ∈ S, (p : ℤ) ∣ z) : ((∏ p ∈ S, p : ℕ) : ℤ) ∣ z := by
  push_cast
  apply Finset.prod_dvd_of_coprime _ h
  intro p hp q hq hpq
  rw [Function.onFun, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

lemma deletedPrimes_prime {n p : ℕ} (hp : p ∈ deletedPrimes n) : p.Prime := by
  unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.1

lemma deletedPrimes_le {n p : ℕ} (hp : p ∈ deletedPrimes n) : p ≤ 8 * n := by
  unfold deletedPrimes at hp
  have := (Finset.mem_filter.mp hp).1; rw [Finset.mem_range] at this; omega

lemma deletedPrimes_sq {n p : ℕ} (hp : p ∈ deletedPrimes n) : 8 * n < p ^ 2 := by
  unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.2.2.1

lemma dvd_lcmUpto' {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : j ∣ Nat.lcmUpto m :=
  Finset.dvd_lcm (s := Finset.Icc 1 m) (f := id) (Finset.mem_Icc.mpr ⟨hj, hjm⟩)

/-- `Φ_n · j` divides `lcm(1..8n) · x` when the deleted primes dividing `j` divide `x`. -/
theorem Phi_mul_dvd (n j : ℕ) (hj : 1 ≤ j) (hj8 : j ≤ 8 * n) (x : ℤ)
    (hx : ∀ p ∈ deletedPrimes n, p ∣ j → (p : ℤ) ∣ x) :
    ((Phi n * j : ℕ) : ℤ) ∣ (Nat.lcmUpto (8 * n) : ℤ) * x := by
  classical
  set S := deletedPrimes n
  set S1 := S.filter (fun p => p ∣ j)
  set S2 := S.filter (fun p => ¬ p ∣ j)
  have hPhi : Phi n = (∏ p ∈ S1, p) * (∏ p ∈ S2, p) := by
    unfold Phi; exact (Finset.prod_filter_mul_prod_filter_not S (fun p => p ∣ j) id).symm
  -- the primes dividing j divide x
  have hg : ((∏ p ∈ S1, p : ℕ) : ℤ) ∣ x :=
    primes_prod_dvd S1 (fun p hp => deletedPrimes_prime (Finset.mem_filter.mp hp).1) x
      (fun p hp => hx p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
  -- the other primes, times j, divide the lcm
  have hcop : Nat.Coprime (∏ p ∈ S2, p) j := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      (deletedPrimes_prime (Finset.mem_filter.mp hp).1)).mpr (Finset.mem_filter.mp hp).2)).symm
  have h2 : (∏ p ∈ S2, p) ∣ Nat.lcmUpto (8 * n) := by
    have := primes_prod_dvd S2 (fun p hp => deletedPrimes_prime (Finset.mem_filter.mp hp).1)
      (Nat.lcmUpto (8 * n) : ℤ) (fun p hp => by
        have hpS := (Finset.mem_filter.mp hp).1
        exact_mod_cast dvd_lcmUpto' (deletedPrimes_prime hpS).one_lt.le (deletedPrimes_le hpS))
    exact_mod_cast this
  have h3 : (∏ p ∈ S2, p) * j ∣ Nat.lcmUpto (8 * n) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 (dvd_lcmUpto' hj hj8)
  obtain ⟨y, hy⟩ := hg
  obtain ⟨z, hz⟩ := h3
  refine ⟨z * y, ?_⟩
  rw [hPhi, hy]
  have : (Nat.lcmUpto (8 * n) : ℤ) = ((∏ p ∈ S2, p : ℕ) : ℤ) * j * z := by exact_mod_cast hz
  rw [this]; push_cast; ring

/-- `Φ_n` divides `ψ_{6n}`. -/
theorem Phi_dvd_psi (n : ℕ) : ((Phi n : ℕ) : ℤ) ∣ psi n (6 * n) := by
  unfold Phi
  exact primes_prod_dvd _ (fun p hp => deletedPrimes_prime hp) _
    (fun p hp => psi_deleted_dvd hp (6 * n) rfl)

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `PF` -/

section
open PowerSeries Polynomial

namespace PiIrrationality.ZZEven.Arith

/-- The truncation `T(w) = Σ_{i ≤ 6n} ψ_i w^i`. -/
noncomputable def Tp (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (6 * n + 1), Polynomial.C (psi n i) * Polynomial.X ^ i

lemma coeff_Tp (n i : ℕ) : (Tp n).coeff i = if i ≤ 6 * n then psi n i else 0 := by
  unfold Tp
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- `Bp = (1-w)^{6n+1} Ψ` as power series. -/
lemma Bp_eq_mul_Psi (n : ℕ) :
    (Bp n : ℤ⟦X⟧) = (1 - PowerSeries.X) ^ (6 * n + 1) * Psi n := by
  rw [Psi, mul_comm (Bp n : ℤ⟦X⟧), ← mul_assoc, mul_comm _ (G (6 * n)), G_mul, one_mul]

/-- `w^{6n+1}` divides `B - (1-w)^{6n+1} T`. -/
lemma X_pow_dvd_Bp_sub (n : ℕ) :
    (Polynomial.X : ℤ[X]) ^ (6 * n + 1) ∣ Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h1 : ((Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n : ℤ[X]) : ℤ⟦X⟧) =
      (1 - PowerSeries.X) ^ (6 * n + 1) * (Psi n - (Tp n : ℤ⟦X⟧)) := by
    rw [Polynomial.coe_sub, Bp_eq_mul_Psi, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
    ring
  have : (Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n).coeff d =
      PowerSeries.coeff d (((Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n : ℤ[X])) : ℤ⟦X⟧) :=
    (Polynomial.coeff_coe _ _).symm
  rw [this, h1, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  rw [map_sub, Polynomial.coeff_coe, coeff_Tp, if_pos (by omega)]
  simp [psi]

/-- `B(1-w) = B(w)`. -/
lemma Bp_comp_one_sub (n : ℕ) : (Bp n).comp (1 - Polynomial.X) = Bp n := by
  unfold Bp
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.one_comp, Polynomial.ofNat_comp]
  push_cast
  have e1 : (2 * (1 - Polynomial.X) - 1 : ℤ[X]) ^ (4 * n) = (2 * Polynomial.X - 1) ^ (4 * n) := by
    rw [show (2 * (1 - Polynomial.X) - 1 : ℤ[X]) = -(2 * Polynomial.X - 1) by ring, neg_pow,
      show (-1 : ℤ[X]) ^ (4 * n) = 1 by rw [pow_mul]; norm_num, one_mul]
  have e2 : (5 * (1 - Polynomial.X) ^ 2 - 4 * (1 - Polynomial.X) + 1 : ℤ[X]) =
      5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2 := by ring
  have e3 : (5 * (1 - Polynomial.X) ^ 2 - 6 * (1 - Polynomial.X) + 2 : ℤ[X]) =
      5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1 := by ring
  rw [e1, e2, e3]; ring

/-- **Partial fractions in `w`**: `B = Q (w(1-w))^{6n+1} + (1-w)^{6n+1} T(w) + w^{6n+1} T(1-w)`. -/
theorem exists_Q (n : ℕ) : ∃ Q : ℤ[X],
    Bp n = Q * (Polynomial.X * (1 - Polynomial.X)) ^ (6 * n + 1) +
      (1 - Polynomial.X) ^ (6 * n + 1) * Tp n +
        Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X) := by
  set F := Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n -
    Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X) with hF
  have d1 : (Polynomial.X : ℤ[X]) ^ (6 * n + 1) ∣ F :=
    dvd_sub (X_pow_dvd_Bp_sub n) (dvd_mul_right _ _)
  have d2 : ((1 - Polynomial.X : ℤ[X])) ^ (6 * n + 1) ∣ F := by
    have h := map_dvd (Polynomial.compRingHom (1 - Polynomial.X : ℤ[X])) (X_pow_dvd_Bp_sub n)
    simp only [Polynomial.coe_compRingHom_apply, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp, Bp_comp_one_sub] at h
    rw [show (1 - (1 - Polynomial.X) : ℤ[X]) = Polynomial.X by ring] at h
    have : F = -(Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n -
        Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X)) + 2 * F := by ring
    rw [hF]
    convert dvd_sub h (dvd_mul_right ((1 - Polynomial.X : ℤ[X]) ^ (6 * n + 1)) (Tp n)) using 1
    ring
  have hcop : IsCoprime ((Polynomial.X : ℤ[X]) ^ (6 * n + 1)) ((1 - Polynomial.X) ^ (6 * n + 1)) :=
    IsCoprime.pow ⟨1, 1, by ring⟩
  obtain ⟨Q, hQ⟩ := hcop.mul_dvd d1 d2
  refine ⟨Q, ?_⟩
  rw [hF] at hQ
  rw [mul_pow]
  linear_combination hQ

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Integral` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-- A fixed choice of the polynomial part `Q`. -/
noncomputable def Qn (n : ℕ) : ℤ[X] := Classical.choose (exists_Q n)

lemma Qn_spec (n : ℕ) :
    Bp n = Qn n * (Polynomial.X * (1 - Polynomial.X)) ^ (6 * n + 1) +
      (1 - Polynomial.X) ^ (6 * n + 1) * Tp n +
        Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X) :=
  Classical.choose_spec (exists_Q n)

/-- Evaluation of an integer polynomial at a complex number. -/
noncomputable abbrev ev (p : ℤ[X]) (w : ℂ) : ℂ := Polynomial.aeval w p

lemma ev_Bp (n : ℕ) (w : ℂ) : ev (Bp n) w =
    (2 * w - 1) ^ (4 * n) * (5 * w ^ 2 - 4 * w + 1) ^ (4 * n) * (5 * w ^ 2 - 6 * w + 2) ^ (4 * n) := by
  simp [Bp, ev, map_ofNat]

lemma ev_Tp (n : ℕ) (w : ℂ) : ev (Tp n) w = ∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) * w ^ i := by
  simp [Tp, ev]

/-- The integrand in the variable `w = (t+5)/10`. -/
lemma R_eq_w (n : ℕ) (t : ℂ) :
    R n t = (16 : ℂ) ^ n / 20 * ev (Bp n) ((t + 5) / 10) /
      (((t + 5) / 10) * (1 - (t + 5) / 10)) ^ (6 * n + 1) := by
  set w := (t + 5) / 10 with hw
  have ht : t = 10 * w - 5 := by rw [hw]; ring
  have e1 : t ^ (4 * n) = 5 ^ (4 * n) * (2 * w - 1) ^ (4 * n) := by
    rw [← mul_pow, ht]; ring_nf
  have e2 : (t ^ 4 + 6 * t ^ 2 + 25) ^ (4 * n) =
      400 ^ (4 * n) * ((5 * w ^ 2 - 4 * w + 1) * (5 * w ^ 2 - 6 * w + 2)) ^ (4 * n) := by
    rw [← mul_pow, ht]; ring_nf
  have e3 : (25 - t ^ 2) ^ (6 * n + 1) = 100 ^ (6 * n + 1) * (w * (1 - w)) ^ (6 * n + 1) := by
    rw [← mul_pow, ht]; ring_nf
  have k : (5 : ℂ) * 5 ^ (4 * n) * 400 ^ (4 * n) * 20 = 16 ^ n * 100 ^ (6 * n + 1) := by
    have h0 : (5 : ℂ) ^ 4 * 400 ^ 4 = 16 * 100 ^ 6 := by norm_num
    calc (5 : ℂ) * 5 ^ (4 * n) * 400 ^ (4 * n) * 20 = 100 * (5 ^ 4 * 400 ^ 4) ^ n := by
          rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ = 100 * (16 * 100 ^ 6) ^ n := by rw [h0]
      _ = 16 ^ n * 100 ^ (6 * n + 1) := by rw [mul_pow, ← pow_mul, pow_succ]; ring
  unfold R
  rw [e1, e2, e3, ev_Bp, mul_pow]
  by_cases hD : (w * (1 - w)) ^ (6 * n + 1) = 0
  · rw [hD]; simp
  · field_simp
    linear_combination ((2 * w - 1) ^ (4 * n) * (5 * w ^ 2 - 4 * w + 1) ^ (4 * n) *
      (5 * w ^ 2 - 6 * w + 2) ^ (4 * n)) * k

/-- Partial fractions in `w`, evaluated at a complex point off `{0, 1}`. -/
lemma pf_eval (n : ℕ) (w : ℂ) (h0 : w ≠ 0) (h1 : 1 - w ≠ 0) :
    ev (Bp n) w / (w * (1 - w)) ^ (6 * n + 1) =
      ev (Qn n) w + ∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) * w ^ i / w ^ (6 * n + 1) +
        ∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) * (1 - w) ^ i / (1 - w) ^ (6 * n + 1) := by
  have h := congrArg (fun p => ev p w) (Qn_spec n)
  simp only [ev, map_add, map_mul, map_pow, map_sub, map_one, Polynomial.aeval_X,
    Polynomial.aeval_comp] at h
  have hT := ev_Tp n w
  have hT' := ev_Tp n (1 - w)
  simp only [ev] at hT hT' ⊢
  rw [h, hT, hT', ← Finset.sum_div, ← Finset.sum_div, mul_pow]
  have hA : w ^ (6 * n + 1) ≠ 0 := pow_ne_zero _ h0
  have hB : (1 - w) ^ (6 * n + 1) ≠ 0 := pow_ne_zero _ h1
  generalize w ^ (6 * n + 1) = A at hA ⊢
  generalize (1 - w) ^ (6 * n + 1) = B at hB ⊢
  field_simp


/-! ### An explicit antiderivative -/

/-- An antiderivative of `Q` over `ℂ`. -/
noncomputable def Qhat (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range ((Qn n).natDegree + 1),
    Polynomial.C (((Qn n).coeff k : ℂ) / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1)

lemma derivative_Qhat (n : ℕ) : Polynomial.derivative (Qhat n) = (Qn n).map (Int.castRingHom ℂ) := by
  ext r
  rw [Polynomial.coeff_derivative, Qhat, Polynomial.finsetSum_coeff, Polynomial.coeff_map]
  simp only [Polynomial.coeff_C_mul_X_pow, add_left_inj]
  rw [Finset.sum_ite_eq]
  have : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  split_ifs with hr
  · push_cast; field_simp; simp
  · rw [Finset.mem_range, not_lt] at hr
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

lemma hasDerivAt_Qhat (n : ℕ) (w : ℂ) : HasDerivAt (fun w => (Qhat n).eval w) (ev (Qn n) w) w := by
  have h := (Qhat n).hasDerivAt w
  rw [derivative_Qhat, Polynomial.eval_map] at h
  have e : ev (Qn n) w = Polynomial.eval₂ (Int.castRingHom ℂ) w (Qn n) := by
    simp only [ev, Polynomial.aeval_def]; rfl
  rw [e]; exact h

lemma hasDerivAt_neg_inv_pow (m : ℕ) (hm : 1 ≤ m) (w : ℂ) (hw : w ≠ 0) :
    HasDerivAt (fun w : ℂ => -(1 / ((m : ℂ) * w ^ m))) (1 / w ^ (m + 1)) w := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h := ((hasDerivAt_pow m w).const_mul (m : ℂ)).inv (mul_ne_zero hm' (pow_ne_zero _ hw))
  have h2 := h.neg
  have hf : (fun w : ℂ => -(1 / ((m : ℂ) * w ^ m))) = -(fun y : ℂ => (m : ℂ) * y ^ m)⁻¹ := by
    funext x; simp [one_div]
  rw [hf]
  refine h2.congr_deriv ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 1 + k - 1 = k by omega]
  field_simp
  ring

lemma hasDerivAt_inv_pow_one_sub (m : ℕ) (hm : 1 ≤ m) (w : ℂ) (hw : 1 - w ≠ 0) :
    HasDerivAt (fun w : ℂ => 1 / ((m : ℂ) * (1 - w) ^ m)) (1 / (1 - w) ^ (m + 1)) w := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h := (hasDerivAt_neg_inv_pow m hm (1 - w) hw).comp w h1
  have h2 := h.neg
  have hf : (fun w : ℂ => 1 / ((m : ℂ) * (1 - w) ^ m)) =
      -((fun w : ℂ => -(1 / ((m : ℂ) * w ^ m))) ∘ (fun w : ℂ => 1 - w)) := by
    funext x; simp
  rw [hf]
  exact h2.congr_deriv (by ring)

/-- The antiderivative `Ξ`. -/
noncomputable def Xi (n : ℕ) (w : ℂ) : ℂ :=
  (Qhat n).eval w +
    ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) *
      (-(1 / (((r + 1 : ℕ) : ℂ) * w ^ (r + 1))) + 1 / (((r + 1 : ℕ) : ℂ) * (1 - w) ^ (r + 1))) +
    (psi n (6 * n) : ℂ) * (Complex.log w - Complex.log (1 - w))

lemma hasDerivAt_Xi (n : ℕ) (w : ℂ) (h0 : w ≠ 0) (h1 : 1 - w ≠ 0) (hs0 : w ∈ slitPlane)
    (hs1 : 1 - w ∈ slitPlane) :
    HasDerivAt (Xi n) (ev (Bp n) w / (w * (1 - w)) ^ (6 * n + 1)) w := by
  have hQ := hasDerivAt_Qhat n w
  have hsum : HasDerivAt (fun w : ℂ => ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) *
      (-(1 / (((r + 1 : ℕ) : ℂ) * w ^ (r + 1))) + 1 / (((r + 1 : ℕ) : ℂ) * (1 - w) ^ (r + 1))))
      (∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) *
        (1 / w ^ (r + 1 + 1) + 1 / (1 - w) ^ (r + 1 + 1))) w := by
    apply HasDerivAt.fun_sum
    intro r _
    exact ((hasDerivAt_neg_inv_pow (r + 1) (by omega) w h0).add
      (hasDerivAt_inv_pow_one_sub (r + 1) (by omega) w h1)).const_mul _
  have hlog : HasDerivAt (fun w : ℂ => Complex.log w - Complex.log (1 - w)) (w⁻¹ + (1 - w)⁻¹) w := by
    have a := Complex.hasDerivAt_log hs0
    have b := (Complex.hasDerivAt_log hs1).comp w ((hasDerivAt_id w).const_sub 1)
    exact (a.sub b).congr_deriv (by simp)
  have htot := (hQ.add hsum).add (hlog.const_mul (psi n (6 * n) : ℂ))
  have hfun : Xi n = ((fun w => (Qhat n).eval w) + fun w : ℂ => ∑ r ∈ Finset.range (6 * n),
      (psi n (6 * n - (r + 1)) : ℂ) *
        (-(1 / (((r + 1 : ℕ) : ℂ) * w ^ (r + 1))) + 1 / (((r + 1 : ℕ) : ℂ) * (1 - w) ^ (r + 1)))) +
      fun y => (psi n (6 * n) : ℂ) * (Complex.log y - Complex.log (1 - y)) := by
    funext x; simp [Xi]
  rw [hfun]
  refine htot.congr_deriv ?_
  rw [pf_eval n w h0 h1]
  -- reindex the two pole sums
  have r1 : ∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) * w ^ i / w ^ (6 * n + 1) =
      ∑ r ∈ Finset.range (6 * n + 1), (psi n (6 * n - r) : ℂ) / w ^ (r + 1) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [show 6 * n + 1 - 1 - r = 6 * n - r by omega]
    rw [show 6 * n + 1 = (6 * n - r) + (r + 1) by omega, pow_add]
    field_simp
  have r2 : ∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) * (1 - w) ^ i / (1 - w) ^ (6 * n + 1) =
      ∑ r ∈ Finset.range (6 * n + 1), (psi n (6 * n - r) : ℂ) / (1 - w) ^ (r + 1) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [show 6 * n + 1 - 1 - r = 6 * n - r by omega]
    rw [show 6 * n + 1 = (6 * n - r) + (r + 1) by omega, pow_add]
    field_simp
  rw [r1, r2, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.sub_zero, zero_add, pow_one, mul_add, Finset.sum_add_distrib]
  simp only [div_eq_mul_inv, one_mul]
  ring


/-! ### The integral via the antiderivative -/

lemma w_props (s : ℝ) :
    ((-1 + (s : ℂ) * I) + 5) / 10 ≠ 0 ∧ 1 - ((-1 + (s : ℂ) * I) + 5) / 10 ≠ 0 ∧
      ((-1 + (s : ℂ) * I) + 5) / 10 ∈ slitPlane ∧ 1 - ((-1 + (s : ℂ) * I) + 5) / 10 ∈ slitPlane := by
  have hre : (((-1 + (s : ℂ) * I) + 5) / 10).re = 2 / 5 := by simp; norm_num
  have hre1 : (1 - ((-1 + (s : ℂ) * I) + 5) / 10).re = 3 / 5 := by simp; norm_num
  refine ⟨fun h => ?_, fun h => ?_, mem_slitPlane_iff.mpr (Or.inl (by rw [hre]; norm_num)),
    mem_slitPlane_iff.mpr (Or.inl (by rw [hre1]; norm_num))⟩
  · rw [h] at hre; norm_num at hre
  · rw [h] at hre1; norm_num at hre1

/-- `Φ(t) = 16^n/2 · Ξ((t+5)/10)` is an antiderivative of `R n` along the segment. -/
lemma hasDerivAt_Phi (n : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℂ => (16 : ℂ) ^ n / 2 * Xi n ((t + 5) / 10)) (R n (-1 + (s : ℂ) * I))
      (-1 + (s : ℂ) * I) := by
  obtain ⟨h0, h1, hs0, hs1⟩ := w_props s
  have hw : HasDerivAt (fun t : ℂ => (t + 5) / 10) (1 / 10) (-1 + (s : ℂ) * I) := by
    simpa using ((hasDerivAt_id (-1 + (s : ℂ) * I)).add_const 5).div_const 10
  have h := (HasDerivAt.comp (x := -1 + (s : ℂ) * I) (hasDerivAt_Xi n _ h0 h1 hs0 hs1) hw).const_mul
    ((16 : ℂ) ^ n / 2)
  refine h.congr_deriv ?_
  rw [R_eq_w]
  ring

lemma R_continuousOn (n : ℕ) :
    ContinuousOn (fun s : ℝ => R n (-1 + (s : ℂ) * I) * I) (Set.uIcc (-2) 2) := by
  apply Continuous.continuousOn
  apply Continuous.mul _ continuous_const
  have hden : ∀ s : ℝ, (25 - (-1 + (s : ℂ) * I) ^ 2) ^ (6 * n + 1) ≠ 0 := by
    intro s
    apply pow_ne_zero
    intro h
    have := congrArg Complex.re h
    simp [pow_two] at this
    nlinarith [sq_nonneg s]
  unfold R
  exact Continuous.div (by fun_prop) (by fun_prop) hden

/-- **The integral through the antiderivative**. -/
theorem J_eq_Xi (n : ℕ) :
    J n = I * ((16 : ℂ) ^ n / 2) * (Xi n ((4 + 2 * I) / 10) - Xi n ((4 - 2 * I) / 10)) := by
  set Φ : ℂ → ℂ := fun t => (16 : ℂ) ^ n / 2 * Xi n ((t + 5) / 10) with hΦ
  have hderiv : ∀ s ∈ Set.uIcc (-2 : ℝ) 2,
      HasDerivAt (fun s : ℝ => Φ (-1 + (s : ℂ) * I)) (R n (-1 + (s : ℂ) * I) * I) s := by
    intro s _
    have hl : HasDerivAt (fun w : ℂ => -1 + w * I) I (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const I).const_add (-1)
    exact ((hasDerivAt_Phi n s).comp (s : ℂ) hl).comp_ofReal
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((R_continuousOn n).intervalIntegrable)
  rw [intervalIntegral.integral_mul_const] at hftc
  have e1 : (-1 + ((2 : ℝ) : ℂ) * I + 5) / 10 = (4 + 2 * I) / 10 := by push_cast; ring
  have e2 : (-1 + ((-2 : ℝ) : ℂ) * I + 5) / 10 = (4 - 2 * I) / 10 := by push_cast; ring
  simp only [hΦ, e1, e2] at hftc
  unfold J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : ∫ s in (-2 : ℝ)..2, R n (-1 + (s : ℂ) * I) =
      ((16 : ℂ) ^ n / 2 * Xi n ((4 + 2 * I) / 10) - (16 : ℂ) ^ n / 2 * Xi n ((4 - 2 * I) / 10)) / I := by
    rw [eq_div_iff hI, hftc]
  rw [this]
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from I_sq]
  ring


/-! ### The logarithmic term gives `π i / 2` -/

lemma arg_one_add_I_div : arg ((1 + I) / 5) = Real.pi / 4 := by
  have h : (1 + I) / 5 = ((Real.sqrt 2 / 5 : ℝ) : ℂ) *
      (Complex.cos (Real.pi / 4 : ℝ) + Complex.sin (Real.pi / 4 : ℝ) * I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    linear_combination (-(1 + I) / 10) * h2
  rw [h, arg_mul_cos_add_sin_mul_I (by positivity)]
  constructor <;> linarith [Real.pi_pos]

lemma log_bracket :
    (Complex.log ((4 + 2 * I) / 10) - Complex.log (1 - (4 + 2 * I) / 10)) -
      (Complex.log ((4 - 2 * I) / 10) - Complex.log (1 - (4 - 2 * I) / 10)) = I * (Real.pi / 2) := by
  set a : ℂ := (4 + 2 * I) / 10 with ha
  set b : ℂ := 1 - (4 - 2 * I) / 10 with hb
  have hca : (4 - 2 * I) / 10 = (starRingEnd ℂ) a := by
    rw [ha]; apply Complex.ext <;> simp [map_ofNat] <;> norm_num
  have hcb : 1 - (4 + 2 * I) / 10 = (starRingEnd ℂ) b := by
    rw [hb]; apply Complex.ext <;> simp [map_ofNat] <;> norm_num
  rw [hca, hcb]
  have hre_a : 0 < a.re := by rw [ha]; norm_num
  have hre_b : 0 < b.re := by rw [hb]; norm_num
  have ha0 : a ≠ 0 := fun h => by rw [h] at hre_a; simp at hre_a
  have hb0 : b ≠ 0 := fun h => by rw [h] at hre_b; simp at hre_b
  have arga := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_a)
  have argb := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_b)
  have hpa : arg a ≠ Real.pi := by
    intro h; rw [h, abs_of_pos Real.pi_pos] at arga; linarith [Real.pi_pos]
  have hpb : arg b ≠ Real.pi := by
    intro h; rw [h, abs_of_pos Real.pi_pos] at argb; linarith [Real.pi_pos]
  have hab : arg a + arg b = Real.pi / 4 := by
    have hmul : a * b = (1 + I) / 5 := by
      rw [ha, hb]; ring_nf; rw [I_sq]; ring
    rw [← arg_one_add_I_div, ← hmul]
    refine (arg_mul ha0 hb0 ?_).symm
    constructor <;> nlinarith [abs_lt.mp arga, abs_lt.mp argb, Real.pi_pos]
  apply Complex.ext
  · simp only [sub_re, Complex.log_re, Complex.norm_conj, mul_re, I_re, I_im, ofReal_re, ofReal_im,
      div_ofNat_re]
    ring_nf; simp
  · simp only [sub_im, Complex.log_im, arg_conj, if_neg hpa, if_neg hpb, mul_im, I_re, I_im,
      div_ofNat_im, ofReal_re, ofReal_im]
    norm_num
    linarith

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Pole` -/

section
open Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

lemma I3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring

/-- Gaussian powers of `2 ± i`. -/
lemma gauss_two (m : ℕ) : ∃ x y : ℤ, (2 + I) ^ m = (x : ℂ) + y * I ∧ (2 - I) ^ m = (x : ℂ) - y * I := by
  induction m with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨x, y, h1, h2⟩ := ih
    refine ⟨2 * x - y, x + 2 * y, ?_, ?_⟩
    · rw [pow_succ, h1]; push_cast; ring_nf; simp only [I_sq, I3]; ring
    · rw [pow_succ, h2]; push_cast; ring_nf; simp only [I_sq, I3]; ring

/-- Gaussian powers of `3 ± i` carry `2^{⌊m/2⌋}`. -/
lemma gauss_three (m : ℕ) : ∃ u v : ℤ, (3 + I) ^ m = 2 ^ (m / 2) * ((u : ℂ) + v * I) ∧
    (3 - I) ^ m = 2 ^ (m / 2) * ((u : ℂ) - v * I) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · exact ⟨1, 0, by simp, by simp⟩
    · exact ⟨3, 1, by simp, by simp⟩
    · obtain ⟨u, v, h1, h2⟩ := ih m (by omega)
      refine ⟨4 * u - 3 * v, 3 * u + 4 * v, ?_, ?_⟩
      · rw [show m + 1 + 1 = m + 2 by ring, pow_add, h1, show (m + 2) / 2 = m / 2 + 1 by omega,
          pow_succ]
        push_cast; ring_nf; simp only [I_sq, I3]; ring
      · rw [show m + 1 + 1 = m + 2 by ring, pow_add, h2, show (m + 2) / 2 = m / 2 + 1 by omega,
          pow_succ]
        push_cast; ring_nf; simp only [I_sq, I3]; ring

/-- The pole bracket at order `m`. -/
noncomputable def pb (m : ℕ) : ℂ :=
  (-(1 / ((m : ℂ) * ((4 + 2 * I) / 10) ^ m)) + 1 / ((m : ℂ) * (1 - (4 + 2 * I) / 10) ^ m)) -
    (-(1 / ((m : ℂ) * ((4 - 2 * I) / 10) ^ m)) + 1 / ((m : ℂ) * (1 - (4 - 2 * I) / 10) ^ m))

lemma inv_m_pow (m : ℕ) (z w : ℂ) (hzw : z * w = 1) :
    1 / ((m : ℂ) * z ^ m) = w ^ m / m := by
  have hw : w = z⁻¹ := (eq_inv_of_mul_eq_one_right hzw)
  rw [hw, inv_pow, div_eq_mul_inv (z ^ m)⁻¹, one_div, mul_inv]; ring

lemma pb_formula (m : ℕ) :
    pb m = ((2 + I) ^ m - (2 - I) ^ m + ((3 + I) ^ m - (3 - I) ^ m) / 2 ^ m) / m := by
  have b1 : (4 + 2 * I) / 10 * (2 - I) = 1 := by ring_nf; rw [I_sq]; ring
  have b2 : (4 - 2 * I) / 10 * (2 + I) = 1 := by ring_nf; rw [I_sq]; ring
  have b3 : (1 - (4 + 2 * I) / 10) * ((3 + I) / 2) = 1 := by ring_nf; rw [I_sq]; ring
  have b4 : (1 - (4 - 2 * I) / 10) * ((3 - I) / 2) = 1 := by ring_nf; rw [I_sq]; ring
  unfold pb
  rw [inv_m_pow m _ _ b1, inv_m_pow m _ _ b2, inv_m_pow m _ _ b3, inv_m_pow m _ _ b4, div_pow, div_pow]
  ring

/-- `I · pb m = -2 (y + v / 2^{m - ⌊m/2⌋}) / m` with integers `y, v`. -/
lemma pb_eq (m : ℕ) : ∃ y v : ℤ,
    I * pb m = -(2 * ((y : ℂ) + v / 2 ^ (m - m / 2))) / m := by
  obtain ⟨x, y, h1, h2⟩ := gauss_two m
  obtain ⟨u, v, h3, h4⟩ := gauss_three m
  refine ⟨y, v, ?_⟩
  rw [pb_formula, h1, h2, h3, h4]
  have h2m : (2 : ℂ) ^ m = 2 ^ (m / 2) * 2 ^ (m - m / 2) := by rw [← pow_add]; congr 1; omega
  rw [h2m]
  have : (2 : ℂ) ^ (m / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  have : (2 : ℂ) ^ (m - m / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring_nf; simp only [I_sq, I3]; ring


lemma deletedPrimes_odd {n p : ℕ} (hp : p ∈ deletedPrimes n) : ¬ (2 : ℤ) ∣ p := by
  have hpr := deletedPrimes_prime hp
  have h5 : 5 < p := by unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.2.1
  intro h
  have : 2 ∣ p := by exact_mod_cast h
  rcases hpr.eq_one_or_self_of_dvd 2 this with h' | h' <;> omega

/-- A deleted prime dividing `2^E x` divides `x`. -/
lemma deleted_dvd_of_two_pow {n p : ℕ} (hp : p ∈ deletedPrimes n) (E : ℕ) (x : ℤ)
    (h : (p : ℤ) ∣ 2 ^ E * x) : (p : ℤ) ∣ x := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (deletedPrimes_prime hp)
  rcases hpr.dvd_or_dvd h with h1 | h1
  · exfalso
    have h2 : (p : ℤ) ∣ 2 := hpr.dvd_of_dvd_pow h1
    have h3 : p ∣ 2 := by exact_mod_cast h2
    have h5 : 5 < p := by unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.2.1
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · exact h1

/-- **The pole terms are integral** (Bai, Lemma 2.6). -/
theorem pole_int (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ,
    (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
      ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1) = z := by
  have hPhi : (0 : ℂ) ≠ (Phi n : ℂ) := by
    have : 0 < Phi n := by
      unfold Phi; exact Finset.prod_pos fun p hp => (deletedPrimes_prime hp).pos
    exact_mod_cast this.ne
  have hterm : ∀ r ∈ Finset.range (6 * n), ∃ z : ℤ,
      (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
        ((psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1)) = z := by
    intro r hr
    rw [Finset.mem_range] at hr
    set m := r + 1 with hm
    have hm6 : m ≤ 6 * n := by omega
    -- 2-adic factor of ψ
    have h2 := psi_two_adic n (6 * n - m)
    have he : 4 * n - (6 * n - m) / 2 = n + (m - m / 2) := by omega
    rw [he] at h2
    obtain ⟨ψ', hψ'⟩ := h2
    -- prime deletion for ψ'
    have hdel : ∀ p ∈ deletedPrimes n, p ∣ m → (p : ℤ) ∣ ψ' := by
      intro p hp hpm
      apply deleted_dvd_of_two_pow hp (n + (m - m / 2))
      rw [← hψ']
      apply psi_deleted_dvd hp
      obtain ⟨c, hc⟩ := hpm
      have : 6 * n = (6 * n - m) + p * c := by omega
      conv_rhs => rw [this]
      rw [Nat.add_mul_mod_self_left]
    obtain ⟨Z, hZ⟩ := Phi_mul_dvd n m (by omega) (by omega) ψ' hdel
    obtain ⟨y, v, hpb⟩ := pb_eq m
    refine ⟨-16 * Z * (2 ^ (m - m / 2) * y + v), ?_⟩
    have hZc : ((Phi n * m : ℕ) : ℂ) * Z = (Nat.lcmUpto (8 * n) : ℂ) * ψ' := by
      exact_mod_cast hZ.symm
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hL : (Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ) * ψ' / m = Z := by
      push_cast at hZc
      field_simp
      linear_combination -hZc
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2e : (2 : ℂ) ^ (m - m / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
    calc (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
          ((psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1))
        = (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) *
          ((2 : ℂ) ^ n * 2 ^ (m - m / 2) * ψ') * (-(2 * ((y : ℂ) + v / 2 ^ (m - m / 2))) / m) := by
          rw [← hpb, ← hm, hψ']; push_cast; rw [pow_add]; ring
      _ = -16 * (2 ^ (m - m / 2) * (y : ℂ) + v) *
          ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ) * ψ' / m) := by
          field_simp
          ring
      _ = _ := by rw [hL]; push_cast; ring
  choose f hf using hterm
  refine ⟨∑ r ∈ (Finset.range (6 * n)).attach, f r.1 r.2, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun r _ => hf r.1 r.2

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Taylor` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-- The negative binomial series over `ℂ`. -/
noncomputable def GC (d : ℕ) : ℂ⟦X⟧ := PowerSeries.mk fun m => ((Nat.choose (d + m) d : ℕ) : ℂ)

lemma GC_mul (d : ℕ) : GC d * (1 - PowerSeries.X) ^ (d + 1) = 1 :=
  mk_add_choose_mul_one_sub_pow_eq_one (S := ℂ) (d := d)

/-- `(X + a)^{-m}` for `a ≠ 0`, as a power series. -/
noncomputable def invA (a : ℂ) (m : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C (a⁻¹ ^ (m + 1)) * PowerSeries.rescale (-a⁻¹) (GC m)

/-- `(b - X)^{-m}` for `b ≠ 0`. -/
noncomputable def invB (b : ℂ) (m : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C (b⁻¹ ^ (m + 1)) * PowerSeries.rescale b⁻¹ (GC m)

lemma invA_mul (a : ℂ) (ha : a ≠ 0) (m : ℕ) :
    (PowerSeries.X + PowerSeries.C a) ^ (m + 1) * invA a m = 1 := by
  have h : (PowerSeries.X + PowerSeries.C a : ℂ⟦X⟧) =
      PowerSeries.C a * PowerSeries.rescale (-a⁻¹) (1 - PowerSeries.X) := by
    rw [map_sub, map_one, PowerSeries.rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul,
      mul_neg, mul_inv_cancel₀ ha, map_neg, map_one]
    ring
  rw [h, mul_pow, invA, ← map_pow, ← map_pow]
  calc PowerSeries.C (a ^ (m + 1)) * PowerSeries.rescale (-a⁻¹) ((1 - PowerSeries.X) ^ (m + 1)) *
        (PowerSeries.C (a⁻¹ ^ (m + 1)) * PowerSeries.rescale (-a⁻¹) (GC m))
      = PowerSeries.C (a ^ (m + 1) * a⁻¹ ^ (m + 1)) *
          PowerSeries.rescale (-a⁻¹) (GC m * (1 - PowerSeries.X) ^ (m + 1)) := by
        rw [map_mul, map_mul]; ring
    _ = 1 := by rw [GC_mul, map_one, ← mul_pow, mul_inv_cancel₀ ha, one_pow, map_one, mul_one]

lemma invB_mul (b : ℂ) (hb : b ≠ 0) (m : ℕ) :
    (PowerSeries.C b - PowerSeries.X) ^ (m + 1) * invB b m = 1 := by
  have h : (PowerSeries.C b - PowerSeries.X : ℂ⟦X⟧) =
      PowerSeries.C b * PowerSeries.rescale b⁻¹ (1 - PowerSeries.X) := by
    rw [map_sub, map_one, PowerSeries.rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hb, map_one, one_mul]
  rw [h, mul_pow, invB, ← map_pow, ← map_pow]
  calc PowerSeries.C (b ^ (m + 1)) * PowerSeries.rescale b⁻¹ ((1 - PowerSeries.X) ^ (m + 1)) *
        (PowerSeries.C (b⁻¹ ^ (m + 1)) * PowerSeries.rescale b⁻¹ (GC m))
      = PowerSeries.C (b ^ (m + 1) * b⁻¹ ^ (m + 1)) *
          PowerSeries.rescale b⁻¹ (GC m * (1 - PowerSeries.X) ^ (m + 1)) := by
        rw [map_mul, map_mul]; ring
    _ = 1 := by rw [GC_mul, map_one, ← mul_pow, mul_inv_cancel₀ hb, one_pow, map_one, mul_one]

lemma coeff_invA (a : ℂ) (m k : ℕ) :
    PowerSeries.coeff k (invA a m) = a⁻¹ ^ (m + 1) * (-a⁻¹) ^ k * (Nat.choose (m + k) m : ℂ) := by
  rw [invA, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, GC, PowerSeries.coeff_mk]; ring

lemma coeff_invB (b : ℂ) (m k : ℕ) :
    PowerSeries.coeff k (invB b m) = b⁻¹ ^ (m + 1) * b⁻¹ ^ k * (Nat.choose (m + k) m : ℂ) := by
  rw [invB, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, GC, PowerSeries.coeff_mk]; ring


/-- The base point `w₀ = (4-2i)/10`. -/
noncomputable def aw : ℂ := (4 - 2 * I) / 10
noncomputable def bw : ℂ := 1 - aw

lemma aw_ne : aw ≠ 0 := by
  unfold aw; intro h; have := congrArg Complex.re h; simp at this
lemma bw_ne : bw ≠ 0 := by
  unfold bw aw; intro h; have := congrArg Complex.re h; simp at this; norm_num at this

/-- The shift `p ↦ p(X + w₀)` over `ℂ`, as a ring hom. -/
noncomputable def shift : ℤ[X] →+* ℂ[X] :=
  (Polynomial.compRingHom (Polynomial.X + Polynomial.C aw)).comp
    (Polynomial.mapRingHom (Int.castRingHom ℂ))

lemma shift_X : shift Polynomial.X = Polynomial.X + Polynomial.C aw := by
  simp [shift]

lemma shift_C (z : ℤ) : shift (Polynomial.C z) = Polynomial.C (z : ℂ) := by
  simp [shift]

/-- `X^{4n}` divides the shifted `B`. -/
lemma X_pow_dvd_shift_Bp (n : ℕ) : (Polynomial.X : ℂ[X]) ^ (4 * n) ∣ shift (Bp n) := by
  have hroot : 5 * aw ^ 2 - 4 * aw + 1 = 0 := by
    unfold aw; ring_nf; rw [I_sq]; ring
  have hfac : (5 * (Polynomial.X + Polynomial.C aw) ^ 2 - 4 * (Polynomial.X + Polynomial.C aw) + 1 :
      ℂ[X]) = Polynomial.X * (5 * Polynomial.X + 10 * Polynomial.C aw - 4) := by
    have : (Polynomial.C (5 * aw ^ 2 - 4 * aw + 1) : ℂ[X]) = 0 := by rw [hroot, map_zero]
    simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_one] at this
    linear_combination this
  unfold Bp
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_one, shift_X]
  rw [hfac, mul_pow]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right _ _) _) _


lemma shift_one_sub : shift (1 - Polynomial.X) = Polynomial.C bw - Polynomial.X := by
  rw [map_sub, map_one, shift_X, bw, map_sub, map_one]; ring

lemma shift_Tp (n : ℕ) : shift (Tp n) =
    ∑ i ∈ Finset.range (6 * n + 1), Polynomial.C (psi n i : ℂ) * (Polynomial.X + Polynomial.C aw) ^ i := by
  simp only [Tp, map_sum, map_mul, map_pow, shift_X, shift_C]

lemma shift_Tp_comp (n : ℕ) : shift ((Tp n).comp (1 - Polynomial.X)) =
    ∑ i ∈ Finset.range (6 * n + 1), Polynomial.C (psi n i : ℂ) * (Polynomial.C bw - Polynomial.X) ^ i := by
  rw [← Polynomial.coe_compRingHom_apply, Tp]
  simp only [map_sum, map_mul, map_pow, Polynomial.coe_compRingHom_apply, Polynomial.C_comp,
    Polynomial.X_comp, shift_C, shift_one_sub]

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `QCoeff` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-! ### Degree of `Q` -/

lemma natDegree_Bp_le (n : ℕ) : (Bp n).natDegree ≤ 20 * n := by
  unfold Bp
  have h1 : ((2 * Polynomial.X - 1 : ℤ[X]) ^ (4 * n)).natDegree ≤ 4 * n := by
    refine (natDegree_pow_le).trans ?_
    have : (2 * Polynomial.X - 1 : ℤ[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have h2 : ((5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1 : ℤ[X]) ^ (4 * n)).natDegree ≤ 8 * n := by
    refine (natDegree_pow_le).trans ?_
    have : (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1 : ℤ[X]).natDegree ≤ 2 := by compute_degree
    nlinarith
  have h3 : ((5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2 : ℤ[X]) ^ (4 * n)).natDegree ≤ 8 * n := by
    refine (natDegree_pow_le).trans ?_
    have : (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2 : ℤ[X]).natDegree ≤ 2 := by compute_degree
    nlinarith
  refine (natDegree_mul_le).trans ?_
  refine (add_le_add (natDegree_mul_le) h3).trans ?_
  omega

lemma natDegree_Tp_le (n : ℕ) : (Tp n).natDegree ≤ 6 * n := by
  unfold Tp
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  refine (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma natDegree_Qn_le (n : ℕ) (hn : 1 ≤ n) : (Qn n).natDegree ≤ 8 * n - 2 := by
  by_cases hQ : Qn n = 0
  · rw [hQ]; simp
  have hspec := Qn_spec n
  have hD : ((Polynomial.X : ℤ[X]) * (1 - Polynomial.X)) ^ (6 * n + 1) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero Polynomial.X_ne_zero (by
      intro h; have := congrArg (Polynomial.eval 0) h; simp at this)
  have hDdeg : (((Polynomial.X : ℤ[X]) * (1 - Polynomial.X)) ^ (6 * n + 1)).natDegree = 12 * n + 2 := by
    rw [natDegree_pow]
    have : ((Polynomial.X : ℤ[X]) * (1 - Polynomial.X)).natDegree = 2 := by
      rw [show ((Polynomial.X : ℤ[X]) * (1 - Polynomial.X)) = -Polynomial.X ^ 2 + Polynomial.X by ring]
      compute_degree!
    rw [this]; ring
  have heq : Qn n * (Polynomial.X * (1 - Polynomial.X)) ^ (6 * n + 1) =
      Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n -
        Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X) := by
    rw [hspec]; ring
  have hle : (Bp n - (1 - Polynomial.X) ^ (6 * n + 1) * Tp n -
      Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X)).natDegree ≤ 20 * n := by
    have a1 : ((1 - Polynomial.X : ℤ[X]) ^ (6 * n + 1) * Tp n).natDegree ≤ 20 * n := by
      refine natDegree_mul_le.trans ?_
      have : ((1 - Polynomial.X : ℤ[X]) ^ (6 * n + 1)).natDegree ≤ 6 * n + 1 := by
        refine natDegree_pow_le.trans ?_
        have : (1 - Polynomial.X : ℤ[X]).natDegree ≤ 1 := by compute_degree
        nlinarith
      have := natDegree_Tp_le n
      omega
    have a2 : ((Polynomial.X : ℤ[X]) ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X)).natDegree ≤ 20 * n := by
      refine natDegree_mul_le.trans ?_
      have : ((Tp n).comp (1 - Polynomial.X)).natDegree ≤ 6 * n := by
        refine natDegree_comp_le.trans ?_
        have h1 : (1 - Polynomial.X : ℤ[X]).natDegree ≤ 1 := by compute_degree
        have := natDegree_Tp_le n
        nlinarith
      rw [natDegree_X_pow]; omega
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
      (max_le (natDegree_Bp_le n) a1)) a2)
  rw [← heq, natDegree_mul hQ hD, hDdeg] at hle
  omega

/-! ### The coefficients of `Q` -/

lemma one_sub_pow_mul_G (d i : ℕ) (hi : i ≤ d) :
    (1 - PowerSeries.X : ℤ⟦X⟧) ^ i * G d = G (d - i) := by
  rw [G_eq_u_pow, G_eq_u_pow, show d + 1 = i + (d - i + 1) by omega, pow_add, ← mul_assoc,
    ← mul_pow, mul_comm (1 - PowerSeries.X), u_mul, one_pow, one_mul]

lemma coeff_G (d k : ℕ) : PowerSeries.coeff k (G d) = (Nat.choose (d + k) d : ℤ) := by
  simp [G]

/-- `q_k = ψ_{6n+1+k} - Σ_{i ≤ 6n} ψ_i C(6n-i+k, 6n-i)`. -/
theorem coeff_Qn (n k : ℕ) : (Qn n).coeff k = psi n (6 * n + 1 + k) -
    ∑ i ∈ Finset.range (6 * n + 1), psi n i * (Nat.choose (6 * n - i + k) (6 * n - i) : ℤ) := by
  have hspec := congrArg (fun p : ℤ[X] => (p : ℤ⟦X⟧) * G (6 * n)) (Qn_spec n)
  have hP : (Bp n : ℤ⟦X⟧) * G (6 * n) = Psi n := rfl
  rw [hP] at hspec
  have e1 : ((Qn n * (Polynomial.X * (1 - Polynomial.X)) ^ (6 * n + 1) : ℤ[X]) : ℤ⟦X⟧) * G (6 * n) =
      PowerSeries.X ^ (6 * n + 1) * (Qn n : ℤ⟦X⟧) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X, mul_pow]
    calc (Qn n : ℤ⟦X⟧) * (PowerSeries.X ^ (6 * n + 1) * (1 - PowerSeries.X) ^ (6 * n + 1)) * G (6 * n)
        = PowerSeries.X ^ (6 * n + 1) * (Qn n : ℤ⟦X⟧) *
          (G (6 * n) * (1 - PowerSeries.X) ^ (6 * n + 1)) := by ring
      _ = _ := by rw [G_mul, mul_one]
  have e2 : (((1 - Polynomial.X) ^ (6 * n + 1) * Tp n : ℤ[X]) : ℤ⟦X⟧) * G (6 * n) = (Tp n : ℤ⟦X⟧) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_X, mul_comm ((1 - PowerSeries.X) ^ (6 * n + 1)), mul_assoc, mul_comm _ (G _),
      G_mul, mul_one]
  have e3 : ((Polynomial.X ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X) : ℤ[X]) : ℤ⟦X⟧) * G (6 * n) =
      PowerSeries.X ^ (6 * n + 1) * ∑ i ∈ Finset.range (6 * n + 1),
        PowerSeries.C (psi n i) * G (6 * n - i) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc]
    congr 1
    rw [Tp]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.X_comp]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, mul_assoc,
      one_sub_pow_mul_G _ _ (by omega)]
  rw [Polynomial.coe_add, Polynomial.coe_add, add_mul, add_mul, e1, e2, e3] at hspec
  have hc := congrArg (PowerSeries.coeff (6 * n + 1 + k)) hspec
  rw [map_add, map_add, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    PowerSeries.coeff_X_pow_mul', if_pos (by omega), Polynomial.coeff_coe,
    Nat.add_sub_cancel_left, Polynomial.coeff_coe, coeff_Tp, if_neg (by omega), map_sum] at hc
  simp only [PowerSeries.coeff_C_mul, coeff_G] at hc
  unfold psi at hc ⊢
  rw [hc]
  ring

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `YOdd` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-- The polynomial-part contribution `Y` to `M_n J_n`. -/
noncomputable def Yc (n : ℕ) : ℂ :=
  (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
    ((Qhat n).eval ((4 + 2 * I) / 10) - (Qhat n).eval ((4 - 2 * I) / 10))

/-- A deleted prime dividing `K` divides `q_{K-1}`. -/
lemma deleted_dvd_coeff_Qn {n p : ℕ} (hp : p ∈ deletedPrimes n) (K : ℕ) (hK : 1 ≤ K)
    (hpK : p ∣ K) : (p : ℤ) ∣ (Qn n).coeff (K - 1) := by
  have hpr := deletedPrimes_prime hp
  rw [coeff_Qn]
  apply dvd_sub
  · apply psi_deleted_dvd hp
    obtain ⟨c, hc⟩ := hpK
    rw [show 6 * n + 1 + (K - 1) = 6 * n + p * c by omega, Nat.add_mul_mod_self_left]
  · apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    set r := 6 * n - i with hr
    by_cases hpr' : p ∣ r
    · apply Dvd.dvd.mul_right
      apply psi_deleted_dvd hp
      obtain ⟨c, hc⟩ := hpr'
      have : 6 * n = i + p * c := by omega
      conv_rhs => rw [this]
      rw [Nat.add_mul_mod_self_left]
    · apply Dvd.dvd.mul_left
      have hr0 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact absurd (h ▸ dvd_zero p) hpr'
        · exact h
      -- C(N, r) * r = C(N, r-1) * K with N = r + K - 1
      have hid : (r + (K - 1)).choose r * r = (r + (K - 1)).choose (r - 1) * K := by
        have := Nat.choose_succ_right_eq (r + (K - 1)) (r - 1)
        rw [show r - 1 + 1 = r by omega, show r + (K - 1) - (r - 1) = K by omega] at this
        exact this
      have h1 : p ∣ (r + (K - 1)).choose r * r := by
        rw [hid]; exact Dvd.dvd.mul_left hpK _
      have h2 : p ∣ (r + (K - 1)).choose r :=
        ((Nat.Prime.dvd_mul hpr).mp h1).resolve_right hpr'
      rw [show r + (K - 1) = 6 * n - i + (K - 1) by rfl] at h2
      exact_mod_cast h2

lemma Qhat_eval (n : ℕ) (w : ℂ) : (Qhat n).eval w =
    ∑ k ∈ Finset.range ((Qn n).natDegree + 1), ((Qn n).coeff k : ℂ) / ((k : ℂ) + 1) * w ^ (k + 1) := by
  simp [Qhat, Polynomial.eval_finsetSum]

/-- `10^E Y` is an integer: the only denominators of `Y` are powers of `2` and `5`. -/
theorem ten_pow_Yc (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (10 : ℂ) ^ (n + (Qn n).natDegree + 1) * Yc n = z := by
  set D := (Qn n).natDegree with hD
  have hD8 : D ≤ 8 * n - 2 := natDegree_Qn_le n hn
  have hPhi : (Phi n : ℂ) ≠ 0 := by
    have : 0 < Phi n := by
      unfold Phi; exact Finset.prod_pos fun p hp => (deletedPrimes_prime hp).pos
    exact_mod_cast this.ne'
  have hterm : ∀ k ∈ Finset.range (D + 1), ∃ z : ℤ,
      (10 : ℂ) ^ (n + D + 1) * ((8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
        (((Qn n).coeff k : ℂ) / ((k : ℂ) + 1) *
          (((4 + 2 * I) / 10) ^ (k + 1) - ((4 - 2 * I) / 10) ^ (k + 1)))) = z := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨Z, hZ⟩ := Phi_mul_dvd n (k + 1) (by omega) (by omega) ((Qn n).coeff k) (fun p hp hpK =>
      by simpa using deleted_dvd_coeff_Qn hp (k + 1) (by omega) hpK)
    obtain ⟨x, y, h1, h2⟩ := gauss_two (k + 1)
    refine ⟨-16 * Z * y * 2 ^ (D + 1) * 5 ^ (n + D - k), ?_⟩
    have hZc : ((Phi n : ℂ) * ((k : ℂ) + 1)) * Z = (Nat.lcmUpto (8 * n) : ℂ) * (Qn n).coeff k := by
      have := congrArg (fun z : ℤ => (z : ℂ)) hZ; push_cast at this; linear_combination -this
    have e1 : ((4 + 2 * I) / 10) ^ (k + 1) = (2 + I) ^ (k + 1) / 5 ^ (k + 1) := by
      rw [← div_pow]; congr 1; ring
    have e2 : ((4 - 2 * I) / 10) ^ (k + 1) = (2 - I) ^ (k + 1) / 5 ^ (k + 1) := by
      rw [← div_pow]; congr 1; ring
    rw [e1, e2, h1, h2]
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h10 : (10 : ℂ) ^ (n + D + 1) = 2 ^ n * 2 ^ (D + 1) * (5 ^ (k + 1) * 5 ^ (n + D - k)) := by
      rw [← pow_add, ← pow_add, show k + 1 + (n + D - k) = n + D + 1 by omega,
        show n + (D + 1) = n + D + 1 by ring, ← mul_pow]
      norm_num
    rw [h10]
    have h5 : (5 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have hZc' : (Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ) * ((Qn n).coeff k : ℂ) / ((k : ℂ) + 1) = Z := by
      field_simp; linear_combination -hZc
    calc (2 : ℂ) ^ n * 2 ^ (D + 1) * (5 ^ (k + 1) * 5 ^ (n + D - k)) *
          ((8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
            (((Qn n).coeff k : ℂ) / ((k : ℂ) + 1) *
              ((x + y * I) / 5 ^ (k + 1) - (x - y * I) / 5 ^ (k + 1))))
        = 8 * 2 ^ (D + 1) * 5 ^ (n + D - k) * (I * (2 * y * I)) *
          ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ) * ((Qn n).coeff k : ℂ) / ((k : ℂ) + 1)) := by
          field_simp; ring
      _ = _ := by rw [hZc']; push_cast; ring_nf; rw [I_sq]; ring
  choose f hf using hterm
  refine ⟨∑ k ∈ (Finset.range (D + 1)).attach, f k.1 k.2, ?_⟩
  rw [Yc, Qhat_eval, Qhat_eval, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun k _ => hf k.1 k.2

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `YFive` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-- Conjugate Gaussian powers. -/
lemma gauss_pow (a b : ℤ) (m : ℕ) : ∃ x y : ℤ,
    ((a : ℂ) + b * I) ^ m = (x : ℂ) + y * I ∧ ((a : ℂ) - b * I) ^ m = (x : ℂ) - y * I := by
  induction m with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨x, y, h1, h2⟩ := ih
    refine ⟨a * x - b * y, a * y + b * x, ?_, ?_⟩
    · rw [pow_succ, h1]; push_cast; ring_nf; simp only [I_sq]; ring
    · rw [pow_succ, h2]; push_cast; ring_nf; simp only [I_sq]; ring

/-- The affine change of variables `w = (t+5)/10` over `ℚ`. -/
noncomputable def wq : ℚ[X] := Polynomial.C (1 / 10 : ℚ) * (Polynomial.X + Polynomial.C 5)

/-- The numerator `5 t^{4n} (t^4+6t^2+25)^{4n}`. -/
noncomputable def Nz (n : ℕ) : ℤ[X] :=
  5 * Polynomial.X ^ (4 * n) * (Polynomial.X ^ 4 + 6 * Polynomial.X ^ 2 + 25) ^ (4 * n)

/-- The monic denominator `(t^2-25)^{6n+1}`. -/
noncomputable def Dz (n : ℕ) : ℤ[X] := (Polynomial.X ^ 2 - 25) ^ (6 * n + 1)

lemma Dz_monic (n : ℕ) : (Dz n).Monic := by
  unfold Dz
  apply Monic.pow
  have : (Polynomial.X ^ 2 - 25 : ℤ[X]) = Polynomial.X ^ 2 - Polynomial.C 25 := by simp
  rw [this]; exact monic_X_pow_sub_C _ (by norm_num)

lemma natDegree_Dz (n : ℕ) : (Dz n).natDegree = 12 * n + 2 := by
  unfold Dz
  rw [natDegree_pow]
  have : (Polynomial.X ^ 2 - 25 : ℤ[X]).natDegree = 2 := by compute_degree!
  rw [this]; ring

/-- The polynomial part in `t`, over `ℚ`. -/
noncomputable def Pq (n : ℕ) : ℚ[X] :=
  Polynomial.C ((2 : ℚ) ^ (4 * n) / 20) * ((Qn n).map (Int.castRingHom ℚ)).comp wq

/-- The remaining (pole) part in `t`, over `ℚ`. -/
noncomputable def Wq (n : ℕ) : ℚ[X] :=
  Polynomial.C ((2 : ℚ) ^ (4 * n) / 20 * 100 ^ (6 * n + 1)) *
    (((1 - Polynomial.X) ^ (6 * n + 1) * Tp n + Polynomial.X ^ (6 * n + 1) *
      (Tp n).comp (1 - Polynomial.X)).map (Int.castRingHom ℚ)).comp wq

lemma natDegree_comp_wq_le (p : ℚ[X]) : (p.comp wq).natDegree ≤ p.natDegree := by
  refine natDegree_comp_le.trans ?_
  have : wq.natDegree ≤ 1 := by unfold wq; compute_degree
  nlinarith

lemma natDegree_Wq_lt (n : ℕ) : (Wq n).natDegree < 12 * n + 2 := by
  unfold Wq
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  refine lt_of_le_of_lt (natDegree_comp_wq_le _) ?_
  refine lt_of_le_of_lt natDegree_map_le ?_
  have a1 : ((1 - Polynomial.X : ℤ[X]) ^ (6 * n + 1) * Tp n).natDegree ≤ 12 * n + 1 := by
    refine natDegree_mul_le.trans ?_
    have : ((1 - Polynomial.X : ℤ[X]) ^ (6 * n + 1)).natDegree ≤ 6 * n + 1 := by
      refine natDegree_pow_le.trans ?_
      have : (1 - Polynomial.X : ℤ[X]).natDegree ≤ 1 := by compute_degree
      nlinarith
    have := natDegree_Tp_le n
    omega
  have a2 : ((Polynomial.X : ℤ[X]) ^ (6 * n + 1) * (Tp n).comp (1 - Polynomial.X)).natDegree ≤
      12 * n + 1 := by
    refine natDegree_mul_le.trans ?_
    have : ((Tp n).comp (1 - Polynomial.X)).natDegree ≤ 6 * n := by
      refine natDegree_comp_le.trans ?_
      have h1 : (1 - Polynomial.X : ℤ[X]).natDegree ≤ 1 := by compute_degree
      have := natDegree_Tp_le n
      nlinarith
    rw [natDegree_X_pow]; omega
  have := natDegree_add_le_of_degree_le a1 a2
  omega

lemma eval_wq (x : ℚ) : wq.eval x = (x + 5) / 10 := by
  simp [wq]; ring

/-- The partial-fraction identity in `t`: `N = -P D + W`. -/
lemma N_eq (n : ℕ) : (Nz n).map (Int.castRingHom ℚ) =
    -(Pq n) * (Dz n).map (Int.castRingHom ℚ) + Wq n := by
  apply Polynomial.funext
  intro t
  have h := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℚ)).eval ((t + 5) / 10)) (Qn_spec n)
  simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  simp only [Nz, Dz, Pq, Wq, Polynomial.eval_map, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_comp, eval_wq, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  set w := (t + 5) / 10 with hw
  have ht : t = 10 * w - 5 := by rw [hw]; ring
  have hB : Polynomial.eval₂ (Int.castRingHom ℚ) w (Bp n) =
      (2 * w - 1) ^ (4 * n) * (5 * w ^ 2 - 4 * w + 1) ^ (4 * n) * (5 * w ^ 2 - 6 * w + 2) ^ (4 * n) := by
    simp only [Bp, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  rw [hB] at h
  have e1 : t ^ (4 * n) = 5 ^ (4 * n) * (2 * w - 1) ^ (4 * n) := by
    rw [← mul_pow, ht]; ring_nf
  have e2 : (t ^ 4 + 6 * t ^ 2 + 25) ^ (4 * n) =
      400 ^ (4 * n) * ((5 * w ^ 2 - 4 * w + 1) * (5 * w ^ 2 - 6 * w + 2)) ^ (4 * n) := by
    rw [← mul_pow, ht]; ring_nf
  have e3 : (t ^ 2 - 25) ^ (6 * n + 1) = -(100 ^ (6 * n + 1) * (w * (1 - w)) ^ (6 * n + 1)) := by
    rw [← mul_pow, ht, show (10 * w - 5) ^ 2 - 25 = -(100 * (w * (1 - w))) by ring, neg_pow,
      pow_succ (-1 : ℚ), pow_mul, show ((-1 : ℚ) ^ 6) = 1 by norm_num, one_pow, one_mul,
      neg_one_mul]
  have k : (5 : ℚ) * 5 ^ (4 * n) * 400 ^ (4 * n) * 20 = 2 ^ (4 * n) * 100 ^ (6 * n + 1) := by
    have h0 : (5 : ℚ) ^ 4 * 400 ^ 4 = 2 ^ 4 * 100 ^ 6 := by norm_num
    calc (5 : ℚ) * 5 ^ (4 * n) * 400 ^ (4 * n) * 20 = 100 * (5 ^ 4 * 400 ^ 4) ^ n := by
          rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ = 100 * (2 ^ 4 * 100 ^ 6) ^ n := by rw [h0]
      _ = 2 ^ (4 * n) * 100 ^ (6 * n + 1) := by rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ]; ring
  have hTp : ∀ x : ℚ, Polynomial.eval₂ (Int.castRingHom ℚ) x (Tp n) =
      ((Tp n).map (Int.castRingHom ℚ)).eval x := fun x => (Polynomial.eval_map _ _).symm
  rw [e1, e2, e3, mul_pow]
  have hcomp : Polynomial.eval₂ (Int.castRingHom ℚ) w ((Tp n).comp (1 - Polynomial.X)) =
      Polynomial.eval₂ (Int.castRingHom ℚ) (1 - w) (Tp n) := by
    rw [Polynomial.eval₂_comp]; simp
  rw [hcomp] at h ⊢
  linear_combination ((2 : ℚ) ^ (4 * n) / 20 * 100 ^ (6 * n + 1)) * h +
    ((2 * w - 1) ^ (4 * n) * (5 * w ^ 2 - 4 * w + 1) ^ (4 * n) * (5 * w ^ 2 - 6 * w + 2) ^ (4 * n) / 20) * k

end PiIrrationality.ZZEven.Arith

namespace PiIrrationality.ZZEven.Arith

/-- The integer polynomial part in `t`. -/
noncomputable def Pz (n : ℕ) : ℤ[X] := -(Nz n /ₘ Dz n)

lemma Pz_map (n : ℕ) : (Pz n).map (Int.castRingHom ℚ) = Pq n := by
  have hmon : ((Dz n).map (Int.castRingHom ℚ)).Monic := (Dz_monic n).map _
  have hdeg : (Wq n).degree < ((Dz n).map (Int.castRingHom ℚ)).degree := by
    apply Polynomial.degree_lt_degree
    rw [(Dz_monic n).natDegree_map, natDegree_Dz]
    exact natDegree_Wq_lt n
  have h := (Polynomial.div_modByMonic_unique (f := (Nz n).map (Int.castRingHom ℚ)) (-(Pq n)) (Wq n) hmon
    ⟨by rw [N_eq n]; ring, hdeg⟩).1
  rw [Pz, Polynomial.map_neg, Polynomial.map_divByMonic _ (Dz_monic n), h, neg_neg]

lemma natDegree_Pz_le (n : ℕ) (hn : 1 ≤ n) : (Pz n).natDegree ≤ 8 * n - 2 := by
  have h := congrArg Polynomial.natDegree (Pz_map n)
  rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ))] at h
  rw [h, Pq]
  refine (natDegree_C_mul_le _ _).trans ((natDegree_comp_wq_le _).trans ?_)
  refine natDegree_map_le.trans (natDegree_Qn_le n hn)

/-- The antiderivative of an integer polynomial over `ℂ`. -/
noncomputable def antider (p : ℤ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    Polynomial.C ((p.coeff k : ℂ) / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1)

lemma derivative_antider (p : ℤ[X]) :
    Polynomial.derivative (antider p) = p.map (Int.castRingHom ℂ) := by
  ext r
  rw [Polynomial.coeff_derivative, antider, Polynomial.finsetSum_coeff, Polynomial.coeff_map]
  simp only [Polynomial.coeff_C_mul_X_pow, add_left_inj]
  rw [Finset.sum_ite_eq]
  have : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  split_ifs with hr
  · push_cast; field_simp; simp
  · rw [Finset.mem_range, not_lt] at hr
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

lemma Qhat_eq_antider (n : ℕ) : Qhat n = antider (Qn n) := rfl

/-- The change of variables over `ℂ`. -/
noncomputable def wc : ℂ[X] := Polynomial.C (1 / 10 : ℂ) * (Polynomial.X + Polynomial.C 5)

lemma Pz_mapC (n : ℕ) : (Pz n).map (Int.castRingHom ℂ) =
    Polynomial.C ((2 : ℂ) ^ (4 * n) / 20) * ((Qn n).map (Int.castRingHom ℂ)).comp wc := by
  have h := congrArg (Polynomial.map (algebraMap ℚ ℂ)) (Pz_map n)
  rw [Polynomial.map_map] at h
  have e : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by ext; simp
  rw [e] at h
  rw [h, Pq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_map, e, wq]
  simp [wc, map_ofNat]

/-- The two antiderivatives differ by a constant. -/
lemma antider_Pz_sub (n : ℕ) (a b : ℂ) :
    (antider (Pz n)).eval b - (antider (Pz n)).eval a =
      (2 : ℂ) ^ (4 * n) / 2 * ((Qhat n).eval ((b + 5) / 10) - (Qhat n).eval ((a + 5) / 10)) := by
  set F := antider (Pz n) - Polynomial.C ((2 : ℂ) ^ (4 * n) / 2) * (Qhat n).comp wc with hF
  have hd : Polynomial.derivative F = 0 := by
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.derivative_comp,
      derivative_antider, Qhat_eq_antider, derivative_antider, Pz_mapC]
    have : Polynomial.derivative wc = Polynomial.C (1 / 10 : ℂ) := by simp [wc]
    rw [this, ← mul_assoc, ← Polynomial.C_mul, sub_eq_zero]
    congr 2; ring
  obtain ⟨c, hc⟩ : ∃ c, F = Polynomial.C c := ⟨_, Polynomial.eq_C_of_derivative_eq_zero hd⟩
  have hb := congrArg (Polynomial.eval b) hc
  have ha := congrArg (Polynomial.eval a) hc
  simp only [hF, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp] at ha hb
  have hw : ∀ x : ℂ, wc.eval x = (x + 5) / 10 := fun x => by simp [wc]; ring
  rw [hw] at ha hb
  linear_combination hb - ha

/-- `2^{5n-4} Φ Y` is an integer: `Y` has no factor `5` in its denominator. -/
theorem five_free_Yc (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (2 : ℂ) ^ (5 * n - 4) * (Phi n : ℂ) * Yc n = z := by
  have hPhi : (Phi n : ℂ) ≠ 0 := by
    have : 0 < Phi n := by
      unfold Phi; exact Finset.prod_pos fun p hp => (deletedPrimes_prime hp).pos
    exact_mod_cast this.ne'
  have hrel := antider_Pz_sub n (-1 - 2 * I) (-1 + 2 * I)
  have e1 : (-1 + 2 * I + 5) / 10 = (4 + 2 * I) / 10 := by ring
  have e2 : (-1 - 2 * I + 5) / 10 = (4 - 2 * I) / 10 := by ring
  rw [e1, e2] at hrel
  set D := (Pz n).natDegree with hD
  have hD8 : D ≤ 8 * n - 2 := natDegree_Pz_le n hn
  have key : (2 : ℂ) ^ (5 * n - 4) * (Phi n : ℂ) * Yc n =
      (Nat.lcmUpto (8 * n) : ℂ) * I *
        ((antider (Pz n)).eval (-1 + 2 * I) - (antider (Pz n)).eval (-1 - 2 * I)) := by
    rw [hrel, Yc]
    have h2 : (2 : ℂ) ^ (4 * n) = 2 ^ n * 2 ^ (5 * n - 4) * 2 ^ 4 / 2 ^ (2 * n) := by
      rw [eq_div_iff (pow_ne_zero _ two_ne_zero), ← pow_add, ← pow_add, ← pow_add]
      congr 1; omega
    rw [h2]
    field_simp
    ring
  rw [key]
  have hterm : ∀ k ∈ Finset.range (D + 1), ∃ z : ℤ,
      (Nat.lcmUpto (8 * n) : ℂ) * I * (((Pz n).coeff k : ℂ) / ((k : ℂ) + 1) *
        ((-1 + 2 * I) ^ (k + 1) - (-1 - 2 * I) ^ (k + 1))) = z := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc⟩ := dvd_lcmUpto' (m := 8 * n) (j := k + 1) (by omega) (by omega)
    obtain ⟨x, y, h1, h2⟩ := gauss_pow (-1) 2 (k + 1)
    push_cast at h1 h2
    refine ⟨-2 * c * (Pz n).coeff k * y, ?_⟩
    rw [h1, h2]
    have hcc : (Nat.lcmUpto (8 * n) : ℂ) = ((k : ℂ) + 1) * c := by exact_mod_cast hc
    rw [hcc]
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    field_simp
    ring_nf; rw [I_sq]; ring
  choose f hf using hterm
  refine ⟨∑ k ∈ (Finset.range (D + 1)).attach, f k.1 k.2, ?_⟩
  simp only [antider, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [← mul_sub]
  push_cast
  rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun k _ => hf k.1 k.2

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `YTwo` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

/-! ### Gaussian integers inside `ℂ` -/

/-- The Gaussian integers as a subring of `ℂ`. -/
def GZ : Subring ℂ where
  carrier := {z | ∃ x y : ℤ, z = x + y * I}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    push_cast; ring_nf; rw [I_sq]; ring
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩

lemma I_mem_GZ : I ∈ GZ := ⟨0, 1, by simp⟩

lemma int_mem_GZ (z : ℤ) : (z : ℂ) ∈ GZ := intCast_mem _ z

lemma nat_mem_GZ (z : ℕ) : (z : ℂ) ∈ GZ := natCast_mem _ z

/-! ### Taylor expansion of `Q` at `w₀` -/

/-- The integer polynomial `Q` over `ℂ`. -/
noncomputable abbrev Qc (n : ℕ) : ℂ[X] := (Qn n).map (Int.castRingHom ℂ)

/-- Taylor coefficients of `Q` at `w₀`. -/
noncomputable def β (n k : ℕ) : ℂ := (Polynomial.taylor aw (Qc n)).coeff k

lemma natDegree_taylor_Qc (n : ℕ) :
    (Polynomial.taylor aw (Qc n)).natDegree ≤ (Qn n).natDegree := by
  rw [Polynomial.natDegree_taylor]; exact natDegree_map_le

/-- An antiderivative of a complex polynomial of degree at most `N`. -/
noncomputable def antiderC (p : ℂ[X]) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1)

lemma derivative_antiderC (p : ℂ[X]) (N : ℕ) (hN : p.natDegree ≤ N) :
    Polynomial.derivative (antiderC p N) = p := by
  ext r
  rw [Polynomial.coeff_derivative, antiderC, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, add_left_inj]
  rw [Finset.sum_ite_eq]
  have : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  split_ifs with hr
  · field_simp
  · rw [Finset.mem_range, not_lt] at hr
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

lemma Qhat_derivative (n : ℕ) : Polynomial.derivative (Qhat n) = Qc n := by
  rw [Qhat_eq_antider, derivative_antider]

/-- `Q̂(w̄₀) - Q̂(w₀) = Σ β_k (2i/5)^{k+1}/(k+1)`. -/
theorem Qhat_diff_taylor (n : ℕ) :
    (Qhat n).eval ((4 + 2 * I) / 10) - (Qhat n).eval ((4 - 2 * I) / 10) =
      ∑ k ∈ Finset.range ((Qn n).natDegree + 1), β n k / ((k : ℂ) + 1) * (2 * I / 5) ^ (k + 1) := by
  set N := (Qn n).natDegree
  set F := (Qhat n).comp (Polynomial.X + Polynomial.C aw) -
    antiderC (Polynomial.taylor aw (Qc n)) N with hF
  have hd : Polynomial.derivative F = 0 := by
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_comp, Qhat_derivative,
      derivative_antiderC _ _ (natDegree_taylor_Qc n), Polynomial.taylor_apply]
    simp
  obtain ⟨c, hc⟩ : ∃ c, F = Polynomial.C c := ⟨_, Polynomial.eq_C_of_derivative_eq_zero hd⟩
  have h1 := congrArg (Polynomial.eval (2 * I / 5)) hc
  have h0 := congrArg (Polynomial.eval 0) hc
  simp only [hF, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] at h1 h0
  have ea : 2 * I / 5 + aw = (4 + 2 * I) / 10 := by unfold aw; ring
  have eb : (0 : ℂ) + aw = (4 - 2 * I) / 10 := by unfold aw; ring
  rw [ea] at h1; rw [eb] at h0
  have hz : (antiderC (Polynomial.taylor aw (Qc n)) N).eval 0 = 0 := by
    simp [antiderC, Polynomial.eval_finsetSum]
  rw [hz] at h0
  have hs : (antiderC (Polynomial.taylor aw (Qc n)) N).eval (2 * I / 5) =
      ∑ k ∈ Finset.range (N + 1), β n k / ((k : ℂ) + 1) * (2 * I / 5) ^ (k + 1) := by
    simp [antiderC, Polynomial.eval_finsetSum, β]
  rw [hs] at h1
  linear_combination h1 - h0

/-! ### `5`-adic bound on `β` -/

lemma five_pow_β (n k : ℕ) : (5 : ℂ) ^ (Qn n).natDegree * β n k ∈ GZ := by
  set D := (Qn n).natDegree
  have hcomp : Polynomial.taylor aw (Qc n) = ∑ j ∈ Finset.range (D + 1),
      Polynomial.C (((Qn n).coeff j : ℤ) : ℂ) * (Polynomial.X + Polynomial.C aw) ^ j := by
    rw [Polynomial.taylor_apply, Polynomial.comp_eq_sum_left,
      Polynomial.sum_over_range' _ (fun _ => by simp) (D + 1)]
    · apply Finset.sum_congr rfl; intro j _; rw [Polynomial.coeff_map]; rfl
    · have : (Qc n).natDegree ≤ D := natDegree_map_le
      omega
  rw [β, hcomp, Polynomial.finsetSum_coeff, Finset.mul_sum]
  apply Subring.sum_mem
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  have hawe : (5 : ℂ) ^ D * aw ^ (j - k) = 5 ^ (D - (j - k)) * (2 - I) ^ (j - k) := by
    unfold aw
    rw [div_pow, show (10 : ℂ) = 2 * 5 by norm_num]
    have : (5 : ℂ) ^ D = 5 ^ (D - (j - k)) * 5 ^ (j - k) := by rw [← pow_add]; congr 1; omega
    rw [this, show (4 - 2 * I : ℂ) = 2 * (2 - I) by ring, mul_pow, mul_pow]
    field_simp
  have : (5 : ℂ) ^ D * (((Qn n).coeff j : ℂ) * (aw ^ (j - k) * (j.choose k : ℂ))) =
      ((Qn n).coeff j : ℂ) * (j.choose k : ℂ) * (5 ^ (D - (j - k)) * (2 - I) ^ (j - k)) := by
    rw [← hawe]; ring
  rw [this]
  refine Subring.mul_mem _ (Subring.mul_mem _ (int_mem_GZ _) (nat_mem_GZ _))
    (Subring.mul_mem _ (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 5) _)
      (Subring.pow_mem _ (Subring.sub_mem _ (by exact_mod_cast nat_mem_GZ 2) I_mem_GZ) _))

/-! ### `β_k` from the partial fractions (for `k < 4n`) -/

lemma XCa_ne (a : ℂ) (ha : a ≠ 0) : (PowerSeries.X + PowerSeries.C a : ℂ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  simp at this; exact ha this

lemma CbX_ne (b : ℂ) (hb : b ≠ 0) : (PowerSeries.C b - PowerSeries.X : ℂ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  simp at this; exact hb this

lemma invA_pow_mul (a : ℂ) (ha : a ≠ 0) (i m : ℕ) (hi : i ≤ m) :
    (PowerSeries.X + PowerSeries.C a) ^ i * invA a m = invA a (m - i) := by
  apply mul_left_cancel₀ (pow_ne_zero (m - i + 1) (XCa_ne a ha))
  rw [invA_mul a ha (m - i), ← mul_assoc, ← pow_add, show m - i + 1 + i = m + 1 by omega,
    invA_mul a ha m]

lemma invB_pow_mul (b : ℂ) (hb : b ≠ 0) (i m : ℕ) (hi : i ≤ m) :
    (PowerSeries.C b - PowerSeries.X) ^ i * invB b m = invB b (m - i) := by
  apply mul_left_cancel₀ (pow_ne_zero (m - i + 1) (CbX_ne b hb))
  rw [invB_mul b hb (m - i), ← mul_assoc, ← pow_add, show m - i + 1 + i = m + 1 by omega,
    invB_mul b hb m]

lemma shift_eq_taylor (p : ℤ[X]) : shift p = Polynomial.taylor aw (p.map (Int.castRingHom ℂ)) := by
  rw [Polynomial.taylor_apply]; rfl

/-- For `k < 4n`, `β_k` is minus the Taylor coefficient of the pole part. -/
theorem β_eq (n k : ℕ) (hk : k < 4 * n) : β n k = -∑ i ∈ Finset.range (6 * n + 1), (psi n i : ℂ) *
    (PowerSeries.coeff k (invA aw (6 * n - i)) + PowerSeries.coeff k (invB bw (6 * n - i))) := by
  have hspec := congrArg shift (Qn_spec n)
  simp only [map_add, map_mul, map_pow, shift_X, shift_one_sub] at hspec
  have hps := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hspec
  simp only [map_add, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_sub] at hps
  rw [shift_Tp, shift_Tp_comp] at hps
  have hsum1 : ((∑ i ∈ Finset.range (6 * n + 1), Polynomial.C (psi n i : ℂ) *
      (Polynomial.X + Polynomial.C aw) ^ i : ℂ[X]) : ℂ⟦X⟧) =
      ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) *
        (PowerSeries.X + PowerSeries.C aw) ^ i := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp only [map_mul, map_pow, map_add, map_sub, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  have hsum2 : ((∑ i ∈ Finset.range (6 * n + 1), Polynomial.C (psi n i : ℂ) *
      (Polynomial.C bw - Polynomial.X) ^ i : ℂ[X]) : ℂ⟦X⟧) =
      ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) *
        (PowerSeries.C bw - PowerSeries.X) ^ i := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp only [map_mul, map_pow, map_add, map_sub, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  rw [hsum1, hsum2] at hps
  set A : ℂ⟦X⟧ := PowerSeries.X + PowerSeries.C aw with hA
  set B : ℂ⟦X⟧ := PowerSeries.C bw - PowerSeries.X with hB
  have hiA := invA_mul aw aw_ne (6 * n)
  have hiB := invB_mul bw bw_ne (6 * n)
  have hmul := congrArg (· * (invA aw (6 * n) * invB bw (6 * n))) hps
  have hR : ((shift (Qn n) : ℂ[X]) : ℂ⟦X⟧) * (A * B) ^ (6 * n + 1) * (invA aw (6 * n) * invB bw (6 * n)) +
      B ^ (6 * n + 1) * (∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * A ^ i) *
        (invA aw (6 * n) * invB bw (6 * n)) +
      A ^ (6 * n + 1) * (∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * B ^ i) *
        (invA aw (6 * n) * invB bw (6 * n)) =
      ((shift (Qn n) : ℂ[X]) : ℂ⟦X⟧) +
        ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * invA aw (6 * n - i) +
        ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * invB bw (6 * n - i) := by
    have e1 : ((shift (Qn n) : ℂ[X]) : ℂ⟦X⟧) * (A * B) ^ (6 * n + 1) *
        (invA aw (6 * n) * invB bw (6 * n)) = ((shift (Qn n) : ℂ[X]) : ℂ⟦X⟧) := by
      calc _ = ((shift (Qn n) : ℂ[X]) : ℂ⟦X⟧) * (A ^ (6 * n + 1) * invA aw (6 * n)) *
            (B ^ (6 * n + 1) * invB bw (6 * n)) := by ring
        _ = _ := by rw [hiA, hiB, mul_one, mul_one]
    have e2 : B ^ (6 * n + 1) * (∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * A ^ i) *
        (invA aw (6 * n) * invB bw (6 * n)) =
        ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * invA aw (6 * n - i) := by
      calc _ = (B ^ (6 * n + 1) * invB bw (6 * n)) *
            ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * (A ^ i * invA aw (6 * n)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by
            rw [hiB, one_mul]
            apply Finset.sum_congr rfl; intro i hi
            rw [Finset.mem_range] at hi
            rw [invA_pow_mul aw aw_ne i (6 * n) (by omega)]
    have e3 : A ^ (6 * n + 1) * (∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * B ^ i) *
        (invA aw (6 * n) * invB bw (6 * n)) =
        ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * invB bw (6 * n - i) := by
      calc _ = (A ^ (6 * n + 1) * invA aw (6 * n)) *
            ∑ i ∈ Finset.range (6 * n + 1), PowerSeries.C (psi n i : ℂ) * (B ^ i * invB bw (6 * n)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by
            rw [hiA, one_mul]
            apply Finset.sum_congr rfl; intro i hi
            rw [Finset.mem_range] at hi
            rw [invB_pow_mul bw bw_ne i (6 * n) (by omega)]
    rw [e1, e2, e3]
  rw [add_mul, add_mul, hR] at hmul
  have hc := congrArg (PowerSeries.coeff k) hmul
  obtain ⟨g, hg⟩ := X_pow_dvd_shift_Bp n
  have hL : PowerSeries.coeff k (((shift (Bp n) : ℂ[X]) : ℂ⟦X⟧) * (invA aw (6 * n) * invB bw (6 * n))) = 0 := by
    rw [hg, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [hL, map_add, map_add, Polynomial.coeff_coe, map_sum, map_sum] at hc
  simp only [PowerSeries.coeff_C_mul] at hc
  rw [β, ← shift_eq_taylor]
  rw [add_assoc, ← Finset.sum_add_distrib] at hc
  simp_rw [mul_add]
  linear_combination -hc

lemma aw_inv : aw⁻¹ = 2 + I :=
  inv_eq_of_mul_eq_one_right (by unfold aw; ring_nf; rw [I_sq]; ring)

lemma bw_inv : bw⁻¹ = (3 - I) / 2 :=
  inv_eq_of_mul_eq_one_right (by unfold bw aw; ring_nf; rw [I_sq]; ring)

lemma gauss_three' (M : ℕ) : ∃ u v : ℤ, (3 - I) ^ M = 2 ^ (M / 2) * ((u : ℂ) - v * I) := by
  obtain ⟨u, v, _, h⟩ := gauss_three M
  exact ⟨u, v, h⟩

/-- **The `2`-adic size of `β_k`** for `k < 4n`. -/
theorem two_adic_β (n k : ℕ) (hk : k < 4 * n) :
    ∃ γ ∈ GZ, (2 : ℂ) ^ (k + 4) * β n k = 2 ^ n * γ := by
  have hterm : ∀ i ∈ Finset.range (6 * n + 1), ∃ γ ∈ GZ, (2 : ℂ) ^ (k + 4) * ((psi n i : ℂ) *
      (PowerSeries.coeff k (invA aw (6 * n - i)) + PowerSeries.coeff k (invB bw (6 * n - i)))) =
      2 ^ n * γ := by
    intro i hi
    rw [Finset.mem_range] at hi
    set m := 6 * n - i with hm
    set M := m + 1 + k with hM
    obtain ⟨ψ', hψ'⟩ := psi_two_adic n i
    obtain ⟨u, v, huv⟩ := gauss_three' M
    obtain ⟨e1, he1⟩ : ∃ e, k + 4 + (4 * n - i / 2) = n + e := ⟨k + 4 + (4 * n - i / 2) - n, by omega⟩
    obtain ⟨e2, he2⟩ : ∃ e, k + 4 + (4 * n - i / 2) + M / 2 = M + (n + e) :=
      ⟨k + 4 + (4 * n - i / 2) + M / 2 - M - n, by omega⟩
    rw [coeff_invA, coeff_invB, aw_inv, bw_inv]
    set C := ((m + k).choose m : ℂ)
    set X1 := (2 + I) ^ (m + 1) * (-(2 + I)) ^ k
    refine ⟨ψ' * (2 ^ e1 * X1 * C + 2 ^ e2 * ((u : ℂ) - v * I) * C), ?_, ?_⟩
    · refine Subring.mul_mem _ (int_mem_GZ _) (Subring.add_mem _ ?_ ?_)
      · refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 2) _)
          (Subring.mul_mem _ (Subring.pow_mem _ (Subring.add_mem _ (by exact_mod_cast nat_mem_GZ 2) I_mem_GZ) _)
            (Subring.pow_mem _ (Subring.neg_mem _ (Subring.add_mem _ (by exact_mod_cast nat_mem_GZ 2) I_mem_GZ)) _)))
          (nat_mem_GZ _)
      · refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 2) _)
          (Subring.sub_mem _ (int_mem_GZ _) (Subring.mul_mem _ (int_mem_GZ _) I_mem_GZ))) (nat_mem_GZ _)
    · have hpsi : (psi n i : ℂ) = 2 ^ (4 * n - i / 2) * ψ' := by rw [hψ']; push_cast; ring
      have hA : (2 : ℂ) ^ (k + 4) * 2 ^ (4 * n - i / 2) = 2 ^ n * 2 ^ e1 := by
        rw [← pow_add, ← pow_add, he1]
      have hB : ((3 - I) / 2) ^ (m + 1) * ((3 - I) / 2) ^ k = 2 ^ (M / 2) * ((u : ℂ) - v * I) / 2 ^ M := by
        rw [← pow_add, div_pow, ← huv]
      have hX : (2 : ℂ) ^ (k + 4) * 2 ^ (4 * n - i / 2) * (2 ^ (M / 2) * ((u : ℂ) - v * I) / 2 ^ M) =
          2 ^ n * 2 ^ e2 * ((u : ℂ) - v * I) := by
        have h2 : (2 : ℂ) ^ (k + 4) * 2 ^ (4 * n - i / 2) * 2 ^ (M / 2) = 2 ^ M * (2 ^ n * 2 ^ e2) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, he2]
        have hM0 : (2 : ℂ) ^ M ≠ 0 := pow_ne_zero _ two_ne_zero
        field_simp
        linear_combination ((u : ℂ) - v * I) * h2
      rw [hpsi, show (m + 1 + k) = M from rfl] at *
      have hB' : ((3 - I) / 2) ^ (m + 1) * ((3 - I) / 2) ^ k * C =
          2 ^ (M / 2) * ((u : ℂ) - v * I) / 2 ^ M * C := by rw [hB]
      calc (2 : ℂ) ^ (k + 4) * (2 ^ (4 * n - i / 2) * ψ' * (X1 * C + ((3 - I) / 2) ^ (m + 1) *
            ((3 - I) / 2) ^ k * C))
          = (2 : ℂ) ^ (k + 4) * (2 ^ (4 * n - i / 2) * ψ' * (X1 * C + 2 ^ (M / 2) * ((u : ℂ) - v * I) /
            2 ^ M * C)) := by rw [hB']
        _ = _ := by linear_combination (ψ' * X1 * C) * hA + (ψ' * C) * hX
  choose f hf1 hf2 using hterm
  refine ⟨-∑ i ∈ (Finset.range (6 * n + 1)).attach, f i.1 i.2, ?_, ?_⟩
  · exact Subring.neg_mem _ (Subring.sum_mem _ fun i _ => hf1 i.1 i.2)
  · rw [β_eq n k hk, mul_neg, Finset.mul_sum, mul_neg, Finset.mul_sum, ← Finset.sum_attach]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf2 i.1 i.2

end PiIrrationality.ZZEven.Arith

end

/-! ## Module `Final` -/

section
open PowerSeries Polynomial Complex

namespace PiIrrationality.ZZEven.Arith

lemma Phi_ne (n : ℕ) : (Phi n : ℂ) ≠ 0 := by
  have : 0 < Phi n := by
    unfold Phi; exact Finset.prod_pos fun p hp => (deletedPrimes_prime hp).pos
  exact_mod_cast this.ne'

/-- `Φ 5^E Y` is a Gaussian integer: `Y` has no factor `2` in its denominator. -/
theorem two_free_Yc (n : ℕ) (hn : 1 ≤ n) :
    ∃ γ ∈ GZ, (Phi n : ℂ) * 5 ^ (2 * (Qn n).natDegree + 1) * Yc n = γ := by
  set D := (Qn n).natDegree with hD
  have hD8 : D ≤ 8 * n - 2 := natDegree_Qn_le n hn
  have hterm : ∀ k ∈ Finset.range (D + 1), ∃ γ ∈ GZ,
      (Phi n : ℂ) * 5 ^ (2 * D + 1) * ((8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
        (β n k / ((k : ℂ) + 1) * (2 * I / 5) ^ (k + 1))) = γ := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc⟩ := dvd_lcmUpto' (m := 8 * n) (j := k + 1) (by omega) (by omega)
    have hL : (Nat.lcmUpto (8 * n) : ℂ) = ((k : ℂ) + 1) * c := by exact_mod_cast hc
    have h5 : (5 : ℂ) ^ (2 * D + 1) = 5 ^ (k + 1) * 5 ^ (2 * D - k) := by
      rw [← pow_add]; congr 1; omega
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hPhi := Phi_ne n
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [hL, h5, div_pow, mul_pow]
    by_cases hk4 : k < 4 * n
    · obtain ⟨γ, hγ, hβ⟩ := two_adic_β n k hk4
      have hβ' : β n k = 2 ^ n * γ / 2 ^ (k + 4) := by
        rw [eq_div_iff (pow_ne_zero _ two_ne_zero)]; linear_combination hβ
      refine ⟨(c : ℂ) * I ^ (k + 2) * 5 ^ (2 * D - k) * γ, ?_, ?_⟩
      · exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (nat_mem_GZ _)
          (Subring.pow_mem _ I_mem_GZ _)) (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 5) _)) hγ
      · rw [hβ']
        field_simp
        ring
    · have hδ := five_pow_β n k
      have hβ' : β n k = ((5 : ℂ) ^ D * β n k) / 5 ^ D := by
        field_simp
      obtain ⟨s, hs⟩ : ∃ s, k + 1 + 3 = n + s := ⟨k + 4 - n, by omega⟩
      have h2 : (2 : ℂ) ^ (k + 1) = 2 ^ n * 2 ^ s / 8 := by
        rw [eq_div_iff (by norm_num), ← pow_add, ← hs]; ring
      have h5' : (5 : ℂ) ^ (2 * D - k) = 5 ^ D * 5 ^ (D - k) := by
        rw [← pow_add]; congr 1; omega
      refine ⟨(c : ℂ) * I ^ (k + 2) * 2 ^ s * 5 ^ (D - k) * ((5 : ℂ) ^ D * β n k), ?_, ?_⟩
      · exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (nat_mem_GZ _)
          (Subring.pow_mem _ I_mem_GZ _)) (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 2) _))
          (Subring.pow_mem _ (by exact_mod_cast nat_mem_GZ 5) _)) hδ
      · rw [h2, h5']
        field_simp
        ring
  choose f hf1 hf2 using hterm
  refine ⟨∑ k ∈ (Finset.range (D + 1)).attach, f k.1 k.2,
    Subring.sum_mem _ fun k _ => hf1 k.1 k.2, ?_⟩
  rw [Yc, Qhat_diff_taylor, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_attach]
  exact Finset.sum_congr rfl fun k _ => hf2 k.1 k.2

/-- **`Y` is an integer** (Bai, Lemma 2.5). -/
theorem Yc_int (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ, Yc n = z := by
  obtain ⟨z1, h1⟩ := ten_pow_Yc n hn
  obtain ⟨γ, hγ, h2⟩ := two_free_Yc n hn
  obtain ⟨z3, h3⟩ := five_free_Yc n hn
  set a := n + (Qn n).natDegree + 1
  set b := 2 * (Qn n).natDegree + 1
  set c := 5 * n - 4
  -- `Φ Y ∈ ℤ[i]`
  have hc1 : IsCoprime ((5 : ℤ) ^ b) ((2 : ℤ) ^ c) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  obtain ⟨u, v, huv⟩ := hc1
  have hPY : (Phi n : ℂ) * Yc n ∈ GZ := by
    have e : (Phi n : ℂ) * Yc n = u * ((Phi n : ℂ) * 5 ^ b * Yc n) + v * ((2 : ℂ) ^ c * (Phi n : ℂ) * Yc n) := by
      have := congrArg (fun z : ℤ => (z : ℂ)) huv
      push_cast at this
      linear_combination (-(Phi n : ℂ) * Yc n) * this
    rw [e, h2, h3]
    exact Subring.add_mem _ (Subring.mul_mem _ (int_mem_GZ _) hγ)
      (Subring.mul_mem _ (int_mem_GZ _) (int_mem_GZ _))
  -- `Y ∈ ℤ[i]`
  have hc2 : IsCoprime ((10 : ℤ) ^ a) (Phi n : ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one, show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num,
      Int.gcd_natCast_natCast]
    unfold Phi
    apply Nat.Coprime.prod_right
    intro p hp
    have hpr := deletedPrimes_prime hp
    have h5 : 5 < p := by unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.2.1
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    apply Nat.Coprime.mul_left
    · exact (Nat.coprime_primes Nat.prime_two hpr).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_five hpr).mpr (by omega)
  obtain ⟨u', v', huv'⟩ := hc2
  have hY : Yc n ∈ GZ := by
    have e : Yc n = u' * ((10 : ℂ) ^ a * Yc n) + v' * ((Phi n : ℂ) * Yc n) := by
      have := congrArg (fun z : ℤ => (z : ℂ)) huv'
      push_cast at this
      linear_combination (-Yc n) * this
    rw [e, h1]
    exact Subring.add_mem _ (Subring.mul_mem _ (int_mem_GZ _) (int_mem_GZ _))
      (Subring.mul_mem _ (int_mem_GZ _) hPY)
  -- `Y` is real
  obtain ⟨x, y, hxy⟩ := hY
  have him : (Yc n).im = 0 := by
    have h10 : (10 : ℂ) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
    have : Yc n = (z1 : ℂ) / 10 ^ a := by rw [eq_div_iff h10, mul_comm, h1]
    rw [this]
    have : ((10 : ℂ) ^ a) = ((10 ^ a : ℝ) : ℂ) := by push_cast; rfl
    rw [this, show (z1 : ℂ) = ((z1 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_div]
    exact Complex.ofReal_im _
  refine ⟨x, ?_⟩
  rw [hxy] at him ⊢
  simp at him
  rw [him]; simp

lemma Xi_diff (n : ℕ) :
    Xi n ((4 + 2 * I) / 10) - Xi n ((4 - 2 * I) / 10) =
      ((Qhat n).eval ((4 + 2 * I) / 10) - (Qhat n).eval ((4 - 2 * I) / 10)) +
        ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1) +
          (psi n (6 * n) : ℂ) * (I * (Real.pi / 2)) := by
  rw [← log_bracket]
  have hs : ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1) =
      ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) *
        (-(1 / (((r + 1 : ℕ) : ℂ) * ((4 + 2 * I) / 10) ^ (r + 1))) +
          1 / (((r + 1 : ℕ) : ℂ) * (1 - (4 + 2 * I) / 10) ^ (r + 1))) -
      ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) *
        (-(1 / (((r + 1 : ℕ) : ℂ) * ((4 - 2 * I) / 10) ^ (r + 1))) +
          1 / (((r + 1 : ℕ) : ℂ) * (1 - (4 - 2 * I) / 10) ^ (r + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold pb; ring
  rw [hs]
  unfold Xi
  ring

/-- **The linear forms** `M_n J_n = U_n + V_n π`. -/
theorem linearForm_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ,
      (PiIrrationality.ZZEven.M n : ℂ) * PiIrrationality.ZZEven.J n =
          (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(PiIrrationality.ZZEven.M n * 16 ^ n *
          (PiIrrationality.ZZEven.coef n : ℝ) / 4) := by
  obtain ⟨y, hy⟩ := Yc_int n hn
  obtain ⟨z, hz⟩ := pole_int n hn
  -- the coefficient of `π`
  obtain ⟨ψ'', hψ''⟩ := psi_two_adic n (6 * n)
  rw [show 4 * n - 6 * n / 2 = n by omega] at hψ''
  have hcop : IsCoprime (Phi n : ℤ) ((2 : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Int.isCoprime_iff_gcd_eq_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      Int.gcd_natCast_natCast]
    unfold Phi
    apply Nat.Coprime.prod_left
    intro p hp
    have hpr := deletedPrimes_prime hp
    have h5 : 5 < p := by unfold deletedPrimes at hp; exact (Finset.mem_filter.mp hp).2.2.1
    exact (Nat.coprime_primes hpr Nat.prime_two).mpr (by omega)
  obtain ⟨w, hw⟩ : (Phi n : ℤ) ∣ ψ'' := by
    have h := Phi_dvd_psi n
    rw [hψ''] at h
    exact hcop.dvd_of_dvd_mul_left h
  have hpsi : (psi n (6 * n) : ℂ) = 2 ^ n * ((Phi n : ℂ) * w) := by
    rw [hψ'', hw]; push_cast; ring
  have hcoef : (coef n : ℤ) = 2 ^ n * ((Phi n : ℤ) * w) := by
    rw [← psi_six_mul_eq_coef n hn, hψ'', hw]
  refine ⟨y + z, -4 * (Nat.lcmUpto (8 * n) : ℤ) * w, ?_, ?_⟩
  · have hM : (PiIrrationality.ZZEven.M n : ℂ) * (I * ((16 : ℂ) ^ n / 2)) =
        (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I := by
      unfold PiIrrationality.ZZEven.M
      push_cast
      have h16 : (16 : ℂ) ^ n = 2 ^ (4 * n) := by rw [pow_mul]; norm_num
      have h5n : (2 : ℂ) ^ (5 * n) = 2 ^ n * 2 ^ (4 * n) := by rw [← pow_add]; ring_nf
      rw [h16, h5n]
      have := Phi_ne n
      field_simp
      ring
    rw [J_eq_Xi, Xi_diff, ← mul_assoc, hM]
    rw [show (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
        (((Qhat n).eval ((4 + 2 * I) / 10) - (Qhat n).eval ((4 - 2 * I) / 10)) +
          ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1) +
            (psi n (6 * n) : ℂ) * (I * (Real.pi / 2))) =
        Yc n + (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
          ∑ r ∈ Finset.range (6 * n), (psi n (6 * n - (r + 1)) : ℂ) * pb (r + 1) +
        (8 : ℂ) / 2 ^ n * ((Nat.lcmUpto (8 * n) : ℂ) / (Phi n : ℂ)) * I *
          ((psi n (6 * n) : ℂ) * (I * (Real.pi / 2))) by unfold Yc; ring]
    rw [hy, hz, hpsi]
    have := Phi_ne n
    have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  · unfold PiIrrationality.ZZEven.M
    have hc : (coef n : ℝ) = 2 ^ n * ((Phi n : ℝ) * w) := by exact_mod_cast hcoef
    rw [hc]
    have hPhi : (Phi n : ℝ) ≠ 0 := by
      have : 0 < Phi n := by
        unfold Phi; exact Finset.prod_pos fun p hp => (deletedPrimes_prime hp).pos
      exact_mod_cast this.ne'
    have h16 : (16 : ℝ) ^ n = 2 ^ (4 * n) := by rw [pow_mul]; norm_num
    have h5n : (2 : ℝ) ^ (5 * n) = 2 ^ n * 2 ^ (4 * n) := by rw [← pow_add]; ring_nf
    rw [h16, h5n]
    push_cast
    field_simp
    ring

end PiIrrationality.ZZEven.Arith

/-- The target statement. -/
theorem PiIrrationality.ZZEven.linearForm' (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ,
      (PiIrrationality.ZZEven.M n : ℂ) * PiIrrationality.ZZEven.J n =
          (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(PiIrrationality.ZZEven.M n * 16 ^ n *
          (PiIrrationality.ZZEven.coef n : ℝ) / 4) :=
  PiIrrationality.ZZEven.Arith.linearForm_main n hn

end

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ,
      (PiIrrationality.ZZEven.M n : ℂ) * PiIrrationality.ZZEven.J n =
          (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(PiIrrationality.ZZEven.M n * 16 ^ n *
          (PiIrrationality.ZZEven.coef n : ℝ) / 4) :=
  PiIrrationality.ZZEven.Arith.linearForm_main n hn
