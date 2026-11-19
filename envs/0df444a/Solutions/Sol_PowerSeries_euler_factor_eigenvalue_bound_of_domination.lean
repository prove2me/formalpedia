-- Prove2me | solution 1 for PowerSeries.euler_factor_eigenvalue_bound_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T17:11:54.043552+00:00
-- url     : https://prove2.me/submissions/b9d02f34-a3e5-4d61-9172-e10ed31ab3f8

import Mathlib

set_option autoImplicit false

namespace UploadRankinEuler


/-!
# S4-Rankin, R1: the Positive Coefficient Lemma (Katz, "L-functions and monodromy: four lectures on Weil II", p.24)

Power series `exp(Σ_m N_m X^m / m)` are handled in the logarithmic-derivative form used by `S4-Lefschetz`: the unique
series `Y` with `Y(0) = 1` and `Y' = Y · A`, `A = Σ_k N_(k+1) X^k`. Coefficients `N_m ≥ 0` for `m ≥ 1` is the same as
`A ≥ 0` coefficientwise.

Over a strictly ordered field `R` in which `1/(n+1) ≥ 0` (`HasInvNat R`: `hasInvNat_real`, and `hasInvNat_complex` for
`ℂ` with `open scoped ComplexOrder`, where `0 ≤ z` means that `z` is real and nonnegative):
* `coeff_succ_of_deriv`: `Y' = Y A` gives `Y_(n+1) (n+1) = Σ_(i+j=n) Y_i A_j`;
* `posCoef_nonneg` (Katz part 1): `A ≥ 0` coefficientwise implies `Y ≥ 0` coefficientwise;
* `posCoef_le` (Katz part 2): `Z' = Z B` with `0 ≤ B ≤ A` coefficientwise implies `0 ≤ Z ≤ Y` coefficientwise;
* `posCoef_sub_nonneg`: the same as `Y - Z ≥ 0`.
Over a field of characteristic `0`: `logDeriv_unique` (uniqueness of `Y`); `logDeriv_mul` (log-derivatives add).
-/


open PowerSeries Finset.HasAntidiagonal

namespace Rankin

noncomputable section

section General

variable {R : Type*} [CommRing R]

/-- The coefficient recursion of `Y' = Y · A`. -/
theorem coeff_succ_of_deriv {Y A : PowerSeries R} (h : derivative R Y = Y * A) (n : ℕ) :
    coeff (n + 1) Y * (n + 1) = ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
  rw [← coeff_derivative, h, coeff_mul]

end General

section Ordered

variable {R : Type*} [Field R] [PartialOrder R] [IsStrictOrderedRing R]

theorem natCast_add_one_pos' (n : ℕ) : (0 : R) < (n : R) + 1 := by
  have h1 : (0 : R) ≤ (n : R) := Nat.cast_nonneg n
  have h2 : (0 : R) < 1 := zero_lt_one
  exact add_pos_of_nonneg_of_pos h1 h2

/-- `HasInvNat R`: the inverses `1/(n+1)` are `≥ 0` (true in `ℝ` and in `ℂ` with `ComplexOrder`). -/
def HasInvNat (R : Type*) [Field R] [PartialOrder R] : Prop := ∀ n : ℕ, 0 ≤ ((n : R) + 1)⁻¹

theorem eq_mul_inv_natCast (a : R) (n : ℕ) : a = a * ((n : R) + 1) * ((n : R) + 1)⁻¹ := by
  rw [mul_assoc, mul_inv_cancel₀ (natCast_add_one_pos' (R := R) n).ne', mul_one]

theorem le_of_mul_natCast_le (hinv : HasInvNat R) {a b : R} {n : ℕ} (h : a * ((n : R) + 1) ≤ b * ((n : R) + 1)) :
    a ≤ b := by
  rw [eq_mul_inv_natCast a n, eq_mul_inv_natCast b n]
  exact mul_le_mul_of_nonneg_right h (hinv n)

/-- **Positive Coefficient Lemma, part 1** (Katz p.24): if `Y(0) = 1`, `Y' = Y A` and every coefficient of `A` is
`≥ 0`, then every coefficient of `Y` is `≥ 0`. (In exponential form: `exp(F)` has coefficients `≥ 0` when `F` has.) -/
theorem posCoef_nonneg (hinv : HasInvNat R) {Y A : PowerSeries R} (h0 : constantCoeff Y = 1) (h : derivative R Y = Y * A)
    (hA : ∀ j, 0 ≤ coeff j A) : ∀ n, 0 ≤ coeff n Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, h0]; exact zero_le_one
    | succ n =>
      have key := coeff_succ_of_deriv h n
      have hs : 0 ≤ ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
        refine Finset.sum_nonneg fun p hp => mul_nonneg (ih p.1 ?_) (hA _)
        have := mem_antidiagonal.mp hp
        omega
      rw [← key, ← zero_mul ((n : R) + 1)] at hs
      exact le_of_mul_natCast_le hinv hs

/-- **Positive Coefficient Lemma, part 2** (Katz p.24): if moreover `Z(0) = 1`, `Z' = Z B` and `0 ≤ B ≤ A`
coefficientwise, then `Z ≤ Y` coefficientwise. (In exponential form: `exp(F) - exp(G) ≥ 0` when `G ≥ 0` and
`F - G ≥ 0`.) -/
theorem posCoef_le (hinv : HasInvNat R) {Y Z A B : PowerSeries R} (hY0 : constantCoeff Y = 1) (hZ0 : constantCoeff Z = 1)
    (hY : derivative R Y = Y * A) (hZ : derivative R Z = Z * B) (hB : ∀ j, 0 ≤ coeff j B)
    (hBA : ∀ j, coeff j B ≤ coeff j A) : ∀ n, coeff n Z ≤ coeff n Y := by
  have hZn := posCoef_nonneg hinv hZ0 hZ hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hY0, hZ0]
    | succ n =>
      have kY := coeff_succ_of_deriv hY n
      have kZ := coeff_succ_of_deriv hZ n
      have hs : ∑ p ∈ antidiagonal n, coeff p.1 Z * coeff p.2 B ≤
          ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := mem_antidiagonal.mp hp
        have h1 := ih p.1 (by omega)
        exact mul_le_mul h1 (hBA _) (hB _) (le_trans (hZn _) h1)
      rw [← kY, ← kZ] at hs
      exact le_of_mul_natCast_le hinv hs

/-- Part 2 in Katz's form: `Y - Z` has coefficients `≥ 0`. -/
theorem posCoef_sub_nonneg (hinv : HasInvNat R) {Y Z A B : PowerSeries R} (hY0 : constantCoeff Y = 1) (hZ0 : constantCoeff Z = 1)
    (hY : derivative R Y = Y * A) (hZ : derivative R Z = Z * B) (hB : ∀ j, 0 ≤ coeff j B)
    (hBA : ∀ j, coeff j B ≤ coeff j A) (n : ℕ) : 0 ≤ coeff n (Y - Z) := by
  rw [map_sub]
  exact sub_nonneg.mpr (posCoef_le hinv hY0 hZ0 hY hZ hB hBA n)

end Ordered

theorem hasInvNat_real : HasInvNat ℝ := fun n => by positivity

open scoped ComplexOrder in
theorem hasInvNat_complex : HasInvNat ℂ := fun n => by
  have h : ((n : ℂ) + 1)⁻¹ = (((n : ℝ) + 1)⁻¹ : ℝ) := by push_cast; rfl
  rw [h]
  exact Complex.zero_le_real.mpr (by positivity)

section Field

variable {E : Type*} [Field E]

/-- Solutions of `Y' = Y A` with `Y(0) = 1` are unique (characteristic `0`). -/
theorem logDeriv_unique [CharZero E] {Y1 Y2 A : PowerSeries E} (h1 : constantCoeff Y1 = 1) (h2 : constantCoeff Y2 = 1)
    (hY1 : derivative E Y1 = Y1 * A) (hY2 : derivative E Y2 = Y2 * A) : Y1 = Y2 := by
  have hu : IsUnit Y2 := by
    rw [PowerSeries.isUnit_iff_constantCoeff, h2]
    exact isUnit_one
  have hu2 : (hu.unit : PowerSeries E) = Y2 := hu.unit_spec
  have hinv : (↑hu.unit⁻¹ : PowerSeries E) * Y2 = 1 := hu.val_inv_mul
  have hZ : derivative E (Y1 * ↑hu.unit⁻¹) = 0 := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv, hu2, hY2, hY1, smul_eq_mul, smul_eq_mul]
    linear_combination (-((↑hu.unit⁻¹ : PowerSeries E) * Y1 * A)) * hinv
  have hc : constantCoeff (↑hu.unit⁻¹ : PowerSeries E) = 1 := by
    have := congrArg constantCoeff hinv
    rwa [map_mul, h2, mul_one, map_one] at this
  have hZ1 : Y1 * ↑hu.unit⁻¹ = 1 :=
    PowerSeries.derivative.ext (by rw [hZ, PowerSeries.derivative_one]) (by rw [map_mul, h1, hc, mul_one, map_one])
  calc Y1 = Y1 * (↑hu.unit⁻¹ * Y2) := by rw [hinv, mul_one]
    _ = (Y1 * ↑hu.unit⁻¹) * Y2 := by ring
    _ = Y2 := by rw [hZ1, one_mul]

/-- Logarithmic derivatives add: if `Y1' = Y1 A1` and `Y2' = Y2 A2` then `(Y1 Y2)' = (Y1 Y2)(A1 + A2)`. -/
theorem logDeriv_mul {Y1 Y2 A1 A2 : PowerSeries E} (hY1 : derivative E Y1 = Y1 * A1)
    (hY2 : derivative E Y2 = Y2 * A2) : derivative E (Y1 * Y2) = (Y1 * Y2) * (A1 + A2) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hY1, hY2]
  ring

end Field

end

end Rankin

/-!
# S4-Rankin, R2: coefficient growth of power series over `ℂ`

`GrowthLE a B` says `‖a n‖ ≤ C (n+1)^J B^n` for some `C`, `J`: the series `Σ a_n X^n` converges on `|X| < 1/B`.
* closure: `growthLE_of_norm_le` (domination), `growthLE_add`, `growthLE_mul` (Cauchy products), `growthLE_poly`
  (polynomials, `B > 0`), `growthLE_geom` (`Σ γ^n X^n` for `‖γ‖ ≤ B`), `growthLE_prod_geom`;
* `geom γ = Σ γ^n X^n`, `geom_mul : geom γ · (1 - γ X) = 1`;
* **`growthLE_of_mul_prod`**: if `L · Π_(γ ∈ S) (1 - γ X) = P` with `‖γ‖ ≤ B` on `S` and `P` of growth `≤ B` (e.g. a
  polynomial), then `L` has growth `≤ B` (a rational function whose poles lie on `|X| ≥ 1/B` converges on `|X| < 1/B`);
* converse for one eigenvalue: `norm_le_of_pow_le`: `‖α‖^k ≤ C (dk+1)^J B^(dk)` for all `k` forces `‖α‖ ≤ B^d`;
* `norm_le_norm_of_nonneg_of_le` (`ComplexOrder`): `0 ≤ z ≤ w` gives `‖z‖ ≤ ‖w‖`.
-/


open PowerSeries Finset.HasAntidiagonal Filter Topology

namespace Rankin

noncomputable section

/-- `GrowthLE a B`: `‖a n‖ ≤ C (n+1)^J B^n` for all `n`, for some `C` and `J`. -/
def GrowthLE (a : ℕ → ℂ) (B : ℝ) : Prop :=
  ∃ (C : ℝ) (J : ℕ), ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n

theorem growth_const_nonneg {a : ℕ → ℂ} {B C : ℝ} {J : ℕ}
    (h : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n) : 0 ≤ C := by
  have := h 0
  simp only [Nat.cast_zero, zero_add, one_pow, mul_one, pow_zero] at this
  exact (norm_nonneg _).trans this

theorem one_le_natCast_add_one (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem growthLE_of_norm_le {a b : ℕ → ℂ} {B : ℝ} (h : ∀ n, ‖a n‖ ≤ ‖b n‖) (hb : GrowthLE b B) :
    GrowthLE a B := by
  obtain ⟨C, J, hC⟩ := hb
  exact ⟨C, J, fun n => (h n).trans (hC n)⟩

theorem growthLE_add {a b : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B) (ha : GrowthLE a B) (hb : GrowthLE b B) :
    GrowthLE (a + b) B := by
  obtain ⟨C1, J1, h1⟩ := ha
  obtain ⟨C2, J2, h2⟩ := hb
  have hC1 := growth_const_nonneg h1
  have hC2 := growth_const_nonneg h2
  refine ⟨C1 + C2, J1 + J2, fun n => ?_⟩
  have hn1 := one_le_natCast_add_one n
  have e1 : ((n : ℝ) + 1) ^ J1 ≤ ((n : ℝ) + 1) ^ (J1 + J2) := pow_le_pow_right₀ hn1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ J2 ≤ ((n : ℝ) + 1) ^ (J1 + J2) := pow_le_pow_right₀ hn1 (by omega)
  have hBn : 0 ≤ B ^ n := pow_nonneg hB n
  rw [Pi.add_apply]
  calc ‖a n + b n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C1 * ((n : ℝ) + 1) ^ J1 * B ^ n + C2 * ((n : ℝ) + 1) ^ J2 * B ^ n := add_le_add (h1 n) (h2 n)
    _ ≤ C1 * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n + C2 * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC1) hBn
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hC2) hBn
    _ = (C1 + C2) * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n := by ring

theorem growthLE_mul {f g : PowerSeries ℂ} {B : ℝ} (hB : 0 ≤ B) (hf : GrowthLE (fun n => coeff n f) B)
    (hg : GrowthLE (fun n => coeff n g) B) : GrowthLE (fun n => coeff n (f * g)) B := by
  obtain ⟨C1, J1, h1⟩ := hf
  obtain ⟨C2, J2, h2⟩ := hg
  have hC1 := growth_const_nonneg h1
  have hC2 := growth_const_nonneg h2
  refine ⟨C1 * C2, J1 + J2 + 1, fun n => ?_⟩
  simp only
  rw [coeff_mul]
  have hterm : ∀ p ∈ antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖ ≤
      C1 * C2 * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n := by
    intro p hp
    have hp' := mem_antidiagonal.mp hp
    rw [norm_mul]
    have hi : ((p.1 : ℝ) + 1) ^ J1 ≤ ((n : ℝ) + 1) ^ J1 := by
      apply pow_le_pow_left₀ (by positivity)
      have : (p.1 : ℝ) ≤ n := by exact_mod_cast (by omega : p.1 ≤ n)
      linarith
    have hj : ((p.2 : ℝ) + 1) ^ J2 ≤ ((n : ℝ) + 1) ^ J2 := by
      apply pow_le_pow_left₀ (by positivity)
      have : (p.2 : ℝ) ≤ n := by exact_mod_cast (by omega : p.2 ≤ n)
      linarith
    have hBn : B ^ n = B ^ p.1 * B ^ p.2 := by rw [← pow_add, hp']
    have hB1 : 0 ≤ B ^ p.1 := pow_nonneg hB _
    have hB2 : 0 ≤ B ^ p.2 := pow_nonneg hB _
    have hA1 : 0 ≤ C1 * ((p.1 : ℝ) + 1) ^ J1 * B ^ p.1 := mul_nonneg (mul_nonneg hC1 (by positivity)) hB1
    calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖
        ≤ (C1 * ((p.1 : ℝ) + 1) ^ J1 * B ^ p.1) * (C2 * ((p.2 : ℝ) + 1) ^ J2 * B ^ p.2) :=
          mul_le_mul (h1 _) (h2 _) (norm_nonneg _) hA1
      _ ≤ (C1 * ((n : ℝ) + 1) ^ J1 * B ^ p.1) * (C2 * ((n : ℝ) + 1) ^ J2 * B ^ p.2) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hC1) hB1
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj hC2) hB2
          · exact mul_nonneg (mul_nonneg hC2 (by positivity)) hB2
          · exact mul_nonneg (mul_nonneg hC1 (by positivity)) hB1
      _ = C1 * C2 * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n := by rw [hBn]; ring
  calc ‖∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g‖
      ≤ ∑ p ∈ antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ antidiagonal n, C1 * C2 * ((n : ℝ) + 1) ^ (J1 + J2) * B ^ n := Finset.sum_le_sum hterm
    _ = C1 * C2 * ((n : ℝ) + 1) ^ (J1 + J2 + 1) * B ^ n := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast
        ring

theorem growthLE_poly (P : Polynomial ℂ) {B : ℝ} (hB : 0 < B) :
    GrowthLE (fun n => coeff n (P : PowerSeries ℂ)) B := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ / B ^ i, 0, fun n => ?_⟩
  simp only
  rw [Polynomial.coeff_coe, pow_zero, mul_one]
  have hBn : 0 < B ^ n := pow_pos hB n
  by_cases hn : n ≤ P.natDegree
  · have hterm : ‖P.coeff n‖ / B ^ n ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ / B ^ i :=
      Finset.single_le_sum (f := fun i => ‖P.coeff i‖ / B ^ i) (fun i _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    calc ‖P.coeff n‖ = ‖P.coeff n‖ / B ^ n * B ^ n := (div_mul_cancel₀ _ hBn.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hterm hBn.le
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => by positivity) hBn.le

theorem growthLE_one {B : ℝ} (hB : 0 < B) : GrowthLE (fun n => coeff n (1 : PowerSeries ℂ)) B := by
  have := growthLE_poly 1 hB
  simpa only [Polynomial.coe_one] using this

/-- The geometric series `Σ_n γ^n X^n`. -/
def geom (γ : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => γ ^ n

theorem geom_mul (γ : ℂ) : geom γ * (1 - PowerSeries.C γ * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_one]
  cases n with
  | zero =>
    rw [← mul_assoc, coeff_zero_mul_X, geom, coeff_mk, pow_zero, sub_zero, if_pos rfl]
  | succ n =>
    rw [← mul_assoc, mul_comm (geom γ), mul_assoc, coeff_C_mul, coeff_succ_mul_X, geom, coeff_mk, coeff_mk,
      if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

theorem growthLE_geom {γ : ℂ} {B : ℝ} (hγ : ‖γ‖ ≤ B) : GrowthLE (fun n => coeff n (geom γ)) B := by
  refine ⟨1, 0, fun n => ?_⟩
  simp only [geom, coeff_mk, norm_pow, pow_zero, mul_one, one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hγ n

theorem growthLE_prod_geom (S : Multiset ℂ) {B : ℝ} (hB : 0 < B) (hS : ∀ γ ∈ S, ‖γ‖ ≤ B) :
    GrowthLE (fun n => coeff n (S.map geom).prod) B := by
  induction S using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using growthLE_one hB
  | cons γ S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact growthLE_mul hB.le (growthLE_geom (hS γ (Multiset.mem_cons_self γ S)))
      (ih fun g hg => hS g (Multiset.mem_cons_of_mem hg))

theorem prod_geom_mul (S : Multiset ℂ) :
    (S.map geom).prod * (S.map fun γ => 1 - PowerSeries.C γ * PowerSeries.X).prod = 1 := by
  rw [← Multiset.prod_map_mul]
  simp only [geom_mul, Multiset.map_const', Multiset.prod_replicate, one_pow]

/-- **Growth of a rational function**: if `L · Π_(γ ∈ S) (1 - γ X) = P` with `‖γ‖ ≤ B` for `γ ∈ S` and `P` of growth
`≤ B` (e.g. a polynomial, `growthLE_poly`), then `L` has growth `≤ B`. -/
theorem growthLE_of_mul_prod {L P : PowerSeries ℂ} (S : Multiset ℂ) {B : ℝ} (hB : 0 < B)
    (hS : ∀ γ ∈ S, ‖γ‖ ≤ B) (hP : GrowthLE (fun n => coeff n P) B)
    (h : L * (S.map fun γ => 1 - PowerSeries.C γ * PowerSeries.X).prod = P) :
    GrowthLE (fun n => coeff n L) B := by
  have hL : L = P * (S.map geom).prod := by
    rw [← h, mul_assoc, mul_comm _ (S.map geom).prod, prod_geom_mul, mul_one]
  rw [hL]
  exact growthLE_mul hB.le hP (growthLE_prod_geom S hB hS)

/-- **One eigenvalue from growth**: if `‖α‖^k ≤ C (dk+1)^J B^(dk)` for all `k` (`d ≥ 1`, `B > 0`), then
`‖α‖ ≤ B^d`. -/
theorem norm_le_of_pow_le {α : ℂ} {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 < B) {C : ℝ} {J : ℕ}
    (h : ∀ k : ℕ, ‖α‖ ^ k ≤ C * (((d * k : ℕ) : ℝ) + 1) ^ J * B ^ (d * k)) : ‖α‖ ≤ B ^ d := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have hBd : 0 < B ^ d := pow_pos hB d
  set ρ := ‖α‖ / B ^ d with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ hBd, one_mul]; exact hlt
  have hρ0 : 0 < ρ := by linarith
  have hC : 1 ≤ C := by
    have := h 0
    simpa using this
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ J / ρ ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_pow_const_div_const_pow_of_one_lt J hρ1).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun k : ℕ => C * (d : ℝ) ^ J * ρ * ((((k + 1 : ℕ) : ℝ)) ^ J / ρ ^ (k + 1))) atTop (𝓝 0) := by
    simpa using h0.const_mul (C * (d : ℝ) ^ J * ρ)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
  have hαk : ‖α‖ ^ k = ρ ^ k * B ^ (d * k) := by
    rw [hρ, div_pow, pow_mul, div_mul_cancel₀ _ (pow_ne_zero _ hBd.ne')]
  have hk' := h k
  rw [hαk] at hk'
  have h1 : ρ ^ k ≤ C * (((d * k : ℕ) : ℝ) + 1) ^ J := le_of_mul_le_mul_right hk' (pow_pos hB _)
  have h2 : (((d * k : ℕ) : ℝ) + 1) ^ J ≤ ((d : ℝ) * ((k : ℝ) + 1)) ^ J := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith
  have h3 : ρ ^ k ≤ C * (d : ℝ) ^ J * ((k : ℝ) + 1) ^ J := by
    calc ρ ^ k ≤ C * (((d * k : ℕ) : ℝ) + 1) ^ J := h1
      _ ≤ C * ((d : ℝ) * ((k : ℝ) + 1)) ^ J := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = C * (d : ℝ) ^ J * ((k : ℝ) + 1) ^ J := by rw [mul_pow]; ring
  have hρk : 0 < ρ ^ k := pow_pos hρ0 k
  have heq : C * (d : ℝ) ^ J * ρ * ((((k + 1 : ℕ) : ℝ)) ^ J / ρ ^ (k + 1)) =
      C * (d : ℝ) ^ J * ((k : ℝ) + 1) ^ J / ρ ^ k := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [heq, div_lt_one hρk] at hk
  linarith

open scoped ComplexOrder in
/-- `0 ≤ z ≤ w` in `ℂ` (`ComplexOrder`: both real) gives `‖z‖ ≤ ‖w‖`. -/
theorem norm_le_norm_of_nonneg_of_le {z w : ℂ} (hz : 0 ≤ z) (hzw : z ≤ w) : ‖z‖ ≤ ‖w‖ := by
  have hw : 0 ≤ w := hz.trans hzw
  rw [← Complex.re_eq_norm.mpr hz, ← Complex.re_eq_norm.mpr hw]
  exact (Complex.le_def.mp hzw).1

end

end Rankin

/-!
# S4-Rankin, R3: one Euler factor and its domination by the `L`-function

For a closed point `x` of degree `d` whose Frobenius has eigenvalues `A` (a multiset over `ℂ`):
* `geomD α d = Σ_k α^k X^(dk) = 1/(1 - α X^d)` (`geomD_mul`), and its logarithmic derivative (`deriv_geomD`);
* `eulerF A d = Π_(α ∈ A) geomD α d = 1/det(1 - X^d Frob_x)`, with `eulerF(0) = 1` and
  `eulerF' = eulerF · Σ_k c_(k+1) X^k`, `c_m = eulerLog A d m = d · Σ_(α ∈ A) α^(m/d)` if `d ∣ m`, else `0`
  (`deriv_eulerF`): `c_m` is the contribution of `x` to the point sum `N_m = Σ_(deg y ∣ m) deg y · Tr(Frob_y^(m/deg y))`;
* **`euler_dom`** (domination of one Euler factor, Katz pp.24-25): if `L(0) = 1`, `L' = L · Σ_k N_(k+1) X^k`, the
  contribution of `x` is real with `0 ≤ c_m ≤ N_m` for `m ≥ 1` (`ComplexOrder`), and `L` has growth `≤ B`
  (e.g. by `growthLE_of_mul_prod`: `L · det(1 - F X | H²_c) = det(1 - F X | H¹_c)` with the `H²_c` eigenvalues of
  absolute value `≤ B`), then every `α ∈ A` has `‖α‖ ≤ B^d`.
-/


open PowerSeries

namespace Rankin

noncomputable section

/-- `Σ_k α^k X^(dk)`. -/
def geomD (α : ℂ) (d : ℕ) : PowerSeries ℂ := PowerSeries.mk fun n => if d ∣ n then α ^ (n / d) else 0

theorem coeff_geomD_mul (α : ℂ) {d : ℕ} (hd : 0 < d) (k : ℕ) : coeff (d * k) (geomD α d) = α ^ k := by
  rw [geomD, coeff_mk, if_pos (dvd_mul_right d k), Nat.mul_div_cancel_left k hd]

theorem constantCoeff_geomD (α : ℂ) (d : ℕ) : constantCoeff (geomD α d) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, geomD, coeff_mk, if_pos (dvd_zero d), Nat.zero_div, pow_zero]

theorem geomD_mul (α : ℂ) {d : ℕ} (hd : 0 < d) :
    geomD α d * (1 - PowerSeries.C α * PowerSeries.X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_one, mul_left_comm, coeff_C_mul, coeff_mul_X_pow', geomD, coeff_mk,
    coeff_mk]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos (dvd_zero d), if_neg (by omega), if_pos rfl, Nat.zero_div, pow_zero, mul_zero, sub_zero]
  · rw [if_neg hn]
    by_cases hdn : d ≤ n
    · rw [if_pos hdn]
      obtain ⟨m, hm⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
      subst hm
      rw [Nat.add_sub_cancel]
      by_cases hdm : d ∣ m
      · rw [if_pos ((Nat.dvd_add_self_right).mpr hdm), if_pos hdm, Nat.add_div_right m hd, pow_succ]
        ring
      · rw [if_neg (fun h => hdm ((Nat.dvd_add_self_right).mp h)), if_neg hdm, mul_zero, sub_zero]
    · rw [if_neg hdn, mul_zero, sub_zero, if_neg]
      intro h
      exact hdn (Nat.le_of_dvd (by omega) h)

theorem coeff_X_pow_pred_mul_geomD (α : ℂ) {d : ℕ} (hd : 0 < d) (j : ℕ) :
    coeff j (PowerSeries.X ^ (d - 1) * geomD α d) = if d ∣ j + 1 then α ^ ((j + 1) / d - 1) else 0 := by
  rw [coeff_X_pow_mul', geomD, coeff_mk]
  by_cases h1 : d - 1 ≤ j
  · rw [if_pos h1]
    obtain ⟨m, hm⟩ : ∃ m, j = m + (d - 1) := ⟨j - (d - 1), by omega⟩
    subst hm
    have hj : m + (d - 1) + 1 = m + d := by omega
    rw [Nat.add_sub_cancel, hj]
    by_cases hdm : d ∣ m
    · rw [if_pos hdm, if_pos ((Nat.dvd_add_self_right).mpr hdm), Nat.add_div_right m hd, Nat.add_sub_cancel]
    · rw [if_neg hdm, if_neg (fun h => hdm ((Nat.dvd_add_self_right).mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

/-- The contribution `c_m` of a point of degree `d` with Frobenius eigenvalues `A` to `N_m`. -/
def eulerLog (A : Multiset ℂ) (d m : ℕ) : ℂ := if d ∣ m then (d : ℂ) * (A.map fun α => α ^ (m / d)).sum else 0

theorem eulerLog_zero (d m : ℕ) : eulerLog 0 d m = 0 := by
  rw [eulerLog]; split_ifs <;> simp

theorem eulerLog_cons (α : ℂ) (A : Multiset ℂ) (d m : ℕ) :
    eulerLog (α ::ₘ A) d m = eulerLog {α} d m + eulerLog A d m := by
  simp only [eulerLog]
  split_ifs
  · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
    ring
  · simp

theorem deriv_geomD (α : ℂ) {d : ℕ} (hd : 0 < d) :
    derivative ℂ (geomD α d) = geomD α d * PowerSeries.mk fun k => eulerLog {α} d (k + 1) := by
  set Y := geomD α d
  set P : PowerSeries ℂ := 1 - PowerSeries.C α * PowerSeries.X ^ d
  have hYP : Y * P = 1 := geomD_mul α hd
  have hDP : derivative ℂ P = -(PowerSeries.C α * ((d : PowerSeries ℂ) * PowerSeries.X ^ (d - 1))) := by
    simp only [P, map_sub, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
      PowerSeries.derivative_one, mul_one, mul_zero, add_zero, zero_sub]
  have h0 : derivative ℂ (Y * P) = 0 := by rw [hYP, PowerSeries.derivative_one]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDP] at h0
  have hY : derivative ℂ Y = Y * (PowerSeries.C (α * d) * (PowerSeries.X ^ (d - 1) * Y)) := by
    have e : derivative ℂ Y = (Y * P) * derivative ℂ Y := by rw [hYP, one_mul]
    rw [e]
    have hdc : (d : PowerSeries ℂ) = PowerSeries.C (d : ℂ) := by simp
    rw [hdc] at h0
    rw [map_mul]
    linear_combination Y * h0
  rw [hY]
  congr 1
  ext j
  rw [coeff_C_mul, coeff_X_pow_pred_mul_geomD α hd, coeff_mk, eulerLog]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  split_ifs with h
  · have hpos : 0 < (j + 1) / d := Nat.div_pos (Nat.le_of_dvd (by omega) h) hd
    obtain ⟨t, ht⟩ : ∃ t, (j + 1) / d = t + 1 := ⟨(j + 1) / d - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ]
    ring
  · rw [mul_zero]

/-- The Euler factor `1/det(1 - X^d Frob_x) = Π_(α ∈ A) geomD α d`. -/
def eulerF (A : Multiset ℂ) (d : ℕ) : PowerSeries ℂ := (A.map fun α => geomD α d).prod

theorem constantCoeff_eulerF (A : Multiset ℂ) (d : ℕ) : constantCoeff (eulerF A d) = 1 := by
  rw [eulerF, map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, constantCoeff_geomD, Multiset.map_const', Multiset.prod_replicate, one_pow]

theorem deriv_eulerF (A : Multiset ℂ) {d : ℕ} (hd : 0 < d) :
    derivative ℂ (eulerF A d) = eulerF A d * PowerSeries.mk fun k => eulerLog A d (k + 1) := by
  induction A using Multiset.induction_on with
  | empty =>
    simp only [eulerF, Multiset.map_zero, Multiset.prod_zero, PowerSeries.derivative_one, one_mul]
    ext k
    simp [eulerLog_zero]
  | cons α A ih =>
    have e : eulerF (α ::ₘ A) d = geomD α d * eulerF A d := by
      rw [eulerF, eulerF, Multiset.map_cons, Multiset.prod_cons]
    rw [e, logDeriv_mul (deriv_geomD α hd) ih]
    congr 1
    ext k
    rw [map_add, coeff_mk, coeff_mk, coeff_mk, eulerLog_cons]

theorem eulerF_mul_prod (A : Multiset ℂ) {d : ℕ} (hd : 0 < d) :
    eulerF A d * (A.map fun α => 1 - PowerSeries.C α * PowerSeries.X ^ d).prod = 1 := by
  rw [eulerF, ← Multiset.prod_map_mul]
  simp only [geomD_mul _ hd, Multiset.map_const', Multiset.prod_replicate, one_pow]

theorem growthLE_one_sub {α : ℂ} {d : ℕ} {B : ℝ} (hB : 0 < B) :
    GrowthLE (fun n => coeff n (1 - PowerSeries.C α * PowerSeries.X ^ d : PowerSeries ℂ)) B := by
  have h := growthLE_poly (1 - Polynomial.C α * Polynomial.X ^ d) hB
  have e : ((1 - Polynomial.C α * Polynomial.X ^ d : Polynomial ℂ) : PowerSeries ℂ) =
      1 - PowerSeries.C α * PowerSeries.X ^ d := by
    simp [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
      Polynomial.coe_X]
  rwa [e] at h

theorem growthLE_prod_one_sub (A : Multiset ℂ) {d : ℕ} {B : ℝ} (hB : 0 < B) :
    GrowthLE (fun n => coeff n (A.map fun α => 1 - PowerSeries.C α * PowerSeries.X ^ d).prod) B := by
  induction A using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using growthLE_one hB
  | cons α A ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact growthLE_mul hB.le (growthLE_one_sub hB) ih

/-- If the Euler factor `eulerF A d` has growth `≤ B`, every `α ∈ A` has `‖α‖ ≤ B^d`. -/
theorem norm_le_of_growthLE_eulerF {A : Multiset ℂ} {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (h : GrowthLE (fun n => coeff n (eulerF A d)) B) : ∀ α ∈ A, ‖α‖ ≤ B ^ d := by
  intro α hα
  obtain ⟨A', rfl⟩ := Multiset.exists_cons_of_mem hα
  have e : eulerF (α ::ₘ A') d * (A'.map fun β => 1 - PowerSeries.C β * PowerSeries.X ^ d).prod = geomD α d := by
    rw [eulerF, Multiset.map_cons, Multiset.prod_cons, mul_assoc, ← eulerF, eulerF_mul_prod A' hd, mul_one]
  have hg : GrowthLE (fun n => coeff n (geomD α d)) B := by
    rw [← e]
    exact growthLE_mul hB.le h (growthLE_prod_one_sub A' hB)
  obtain ⟨C, J, hC⟩ := hg
  refine norm_le_of_pow_le hd hB (C := C) (J := J) fun k => ?_
  have := hC (d * k)
  simp only at this
  rwa [coeff_geomD_mul α hd, norm_pow] at this

open scoped ComplexOrder in
/-- **Domination of one Euler factor** (Katz pp.24-25, with the Positive Coefficient Lemma): let `L(0) = 1`,
`L' = L · Σ_k N_(k+1) X^k`, and let a point of degree `d` with Frobenius eigenvalues `A` contribute `c_m = eulerLog A d m`
to `N_m`, with `0 ≤ c_m ≤ N_m` (real) for `m ≥ 1`. If `L` has growth `≤ B` (`B > 0`), then `‖α‖ ≤ B^d` for `α ∈ A`. -/
theorem euler_dom {L : PowerSeries ℂ} {N : ℕ → ℂ} (hL0 : constantCoeff L = 1)
    (hL : derivative ℂ L = L * PowerSeries.mk fun k => N (k + 1)) (A : Multiset ℂ) {d : ℕ} (hd : 0 < d)
    (hc : ∀ m, 1 ≤ m → 0 ≤ eulerLog A d m) (hcN : ∀ m, 1 ≤ m → eulerLog A d m ≤ N m) {B : ℝ} (hB : 0 < B)
    (hLg : GrowthLE (fun n => coeff n L) B) : ∀ α ∈ A, ‖α‖ ≤ B ^ d := by
  have hZ := deriv_eulerF A hd
  have hZ0 := constantCoeff_eulerF A d
  have hBc : ∀ j, 0 ≤ coeff j (PowerSeries.mk fun k => eulerLog A d (k + 1)) := fun j => by
    rw [coeff_mk]; exact hc (j + 1) (by omega)
  have hBA : ∀ j, coeff j (PowerSeries.mk fun k => eulerLog A d (k + 1)) ≤
      coeff j (PowerSeries.mk fun k => N (k + 1)) := fun j => by
    rw [coeff_mk, coeff_mk]; exact hcN (j + 1) (by omega)
  have hle := posCoef_le hasInvNat_complex hL0 hZ0 hL hZ hBc hBA
  have hnn := posCoef_nonneg hasInvNat_complex hZ0 hZ hBc
  refine norm_le_of_growthLE_eulerF hd hB (growthLE_of_norm_le (fun n => ?_) hLg)
  exact norm_le_norm_of_nonneg_of_le (hnn n) (hle n)

end

end Rankin

open PowerSeries
open scoped ComplexOrder

theorem main (L : PowerSeries ℂ) (N : ℕ → ℝ)
    (hL0 : PowerSeries.constantCoeff L = 1)
    (hL : PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ)))
    (A : Multiset ℂ) (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ)
    (hcA : ∀ m : ℕ, 1 ≤ m →
      (if d ∣ m then (d : ℂ) * (A.map fun α => α ^ (m / d)).sum else 0) = (c m : ℂ))
    (hc : ∀ m : ℕ, 1 ≤ m → 0 ≤ c m) (hcN : ∀ m : ℕ, 1 ≤ m → c m ≤ N m)
    (B : ℝ) (hB : 0 < B) (C : ℝ) (J : ℕ)
    (hLg : ∀ n : ℕ, ‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n) :
    ∀ α ∈ A, ‖α‖ ≤ B ^ d := by
  have hc' : ∀ m, 1 ≤ m → 0 ≤ Rankin.eulerLog A d m := fun m hm => by
    rw [Rankin.eulerLog, hcA m hm]
    exact Complex.zero_le_real.mpr (hc m hm)
  have hcN' : ∀ m, 1 ≤ m → Rankin.eulerLog A d m ≤ (fun m => ((N m : ℝ) : ℂ)) m := fun m hm => by
    rw [Rankin.eulerLog, hcA m hm]
    exact Complex.real_le_real.mpr (hcN m hm)
  have hg : Rankin.GrowthLE (fun n => coeff n L) B := by
    unfold Rankin.GrowthLE
    exact ⟨C, J, fun n => hLg n⟩
  exact Rankin.euler_dom hL0 hL A hd hc' hcN' hB hg

end UploadRankinEuler

theorem solution (L : PowerSeries ℂ) (N : ℕ → ℝ)
    (hL0 : PowerSeries.constantCoeff L = 1)
    (hL : PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ)))
    (A : Multiset ℂ) (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ)
    (hcA : ∀ m : ℕ, 1 ≤ m →
      (if d ∣ m then (d : ℂ) * (A.map fun α => α ^ (m / d)).sum else 0) = (c m : ℂ))
    (hc : ∀ m : ℕ, 1 ≤ m → 0 ≤ c m) (hcN : ∀ m : ℕ, 1 ≤ m → c m ≤ N m)
    (B : ℝ) (hB : 0 < B) (C : ℝ) (J : ℕ)
    (hLg : ∀ n : ℕ, ‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n) :
    ∀ α ∈ A, ‖α‖ ≤ B ^ d := by
  exact UploadRankinEuler.main L N hL0 hL A d hd c hcA hc hcN B hB C J hLg
