-- Prove2me | solution 1 for WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3c1c6bee-f15c-5fa1-b77c-c8a9b8f74fca

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_LaurentSeries_derivative_mul
import Theorems.Thm_LaurentSeries_coeff_neg_one_inv_mul_derivative
import Theorems.Thm_LaurentSeries_coeff_neg_one_mul_inv_pow_uniformizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open HahnSeries Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map b₂ twoTorsionPolynomial a₄ a₂ a₆ b₆ j b₄ hasseInvariant"
namespace KATZ
p2m_open "WeierstrassCurve"

variable {R : Type*} [CommRing R]

theorem coeff_derivative (x : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.derivative R x).coeff n = ((n + 1 : ℤ) : R) * x.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  push_cast
  ring_nf

theorem res_derivative (x : LaurentSeries R) : (LaurentSeries.derivative R x).coeff (-1) = 0 := by
  rw [coeff_derivative]; simp

theorem derivative_pow_succ (G : LaurentSeries R) (n : ℕ) :
    LaurentSeries.derivative R (G ^ (n + 1)) = ((n + 1 : ℕ) : LaurentSeries R) * (G ^ n * LaurentSeries.derivative R G) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LaurentSeries.derivative_mul, ih]
    push_cast
    ring

theorem coeff_natCast_mul (n : ℕ) (x : LaurentSeries R) (k : ℤ) :
    ((n : LaurentSeries R) * x).coeff k = (n : R) * x.coeff k := by
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) n, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_C_mul (r : R) (x : LaurentSeries R) (k : ℤ) :
    (HahnSeries.C r * x).coeff k = r * x.coeff k := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem res_pow_mul_derivative (G : LaurentSeries R) (n : ℕ) (hu : IsUnit ((n + 1 : ℕ) : R)) :
    (G ^ n * LaurentSeries.derivative R G).coeff (-1) = 0 := by
  have h := congrArg (fun w : LaurentSeries R => w.coeff (-1)) (derivative_pow_succ G n)
  simp only [res_derivative, coeff_natCast_mul] at h
  exact (hu.mul_right_eq_zero).mp h.symm

theorem derivative_one : LaurentSeries.derivative R (1 : LaurentSeries R) = 0 := by
  ext n
  rw [coeff_derivative, HahnSeries.coeff_one, HahnSeries.coeff_zero]
  split_ifs with h
  · have : n + 1 = 0 := h; rw [this]; simp
  · rw [mul_zero]

theorem derivative_inv {G H : LaurentSeries R} (h : G * H = 1) :
    LaurentSeries.derivative R H = -(H ^ 2 * LaurentSeries.derivative R G) := by
  have h1 := congrArg (LaurentSeries.derivative R) h
  rw [LaurentSeries.derivative_mul, derivative_one] at h1

  have h2 : H * (LaurentSeries.derivative R G * H + G * LaurentSeries.derivative R H) = 0 := by rw [h1, mul_zero]
  have h3 : H * (LaurentSeries.derivative R G * H + G * LaurentSeries.derivative R H) =
      H ^ 2 * LaurentSeries.derivative R G + (G * H) * LaurentSeries.derivative R H := by ring
  rw [h3, h, one_mul] at h2
  linear_combination h2

theorem res_inv_pow_mul_derivative {G H : LaurentSeries R} (h : G * H = 1) (k : ℕ) (hk : 2 ≤ k)
    (hu : IsUnit ((k - 1 : ℕ) : R)) :
    (H ^ k * LaurentSeries.derivative R G).coeff (-1) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩

  have hd : LaurentSeries.derivative R (H ^ (j + 1)) =
      -(((j + 1 : ℕ) : LaurentSeries R) * (H ^ (j + 2) * LaurentSeries.derivative R G)) := by
    rw [derivative_pow_succ, derivative_inv h]; ring
  have h1 := congrArg (fun w : LaurentSeries R => w.coeff (-1)) hd
  simp only [res_derivative, HahnSeries.coeff_neg, coeff_natCast_mul] at h1
  have hu' : IsUnit ((j + 1 : ℕ) : R) := by rw [show j + 2 - 1 = j + 1 by omega] at hu; exact hu
  have h2 : ((j + 1 : ℕ) : R) * (H ^ (j + 2) * LaurentSeries.derivative R G).coeff (-1) = 0 := by
    have := h1.symm; rwa [neg_eq_zero] at this
  exact (hu'.mul_right_eq_zero).mp h2

theorem coeff_mul_eq_zero_of_lt {a b : LaurentSeries R} {A B : ℤ} (ha : ∀ n < A, a.coeff n = 0)
    (hb : ∀ n < B, b.coeff n = 0) {n : ℤ} (hn : n < A + B) : (a * b).coeff n = 0 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  exfalso
  by_cases hi : ij.1 < A
  · exact (HahnSeries.mem_support _ _).mp h1 (ha _ hi)
  · exact (HahnSeries.mem_support _ _).mp h2 (hb _ (by omega))

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries R) (n : ℤ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih]

theorem coeff_single_mul_ofPowerSeries (k : ℤ) (P : PowerSeries R) (n : ℤ) :
    (single k (1 : R) * HahnSeries.ofPowerSeries ℤ R P).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs P := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := HahnSeries.ofPowerSeries ℤ R P) (a := n - k) (b := k)
  rw [sub_add_cancel, one_mul] at h
  rw [h]
  exact PowerSeries.coeff_coe P (n - k)

theorem single_mul_ofPowerSeries_coeff_lt (k : ℤ) (P : PowerSeries R) {n : ℤ} (hn : n < k) :
    (single k (1 : R) * HahnSeries.ofPowerSeries ℤ R P).coeff n = 0 := by
  rw [coeff_single_mul_ofPowerSeries, if_pos (by omega)]

theorem single_mul_ofPowerSeries_coeff_self (k : ℤ) (P : PowerSeries R) :
    (single k (1 : R) * HahnSeries.ofPowerSeries ℤ R P).coeff k = PowerSeries.constantCoeff P := by
  rw [coeff_single_mul_ofPowerSeries, if_neg (by omega), show (k - k).natAbs = 0 by simp,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem eq_single_mul_powerSeriesPart [Nontrivial R] {x : LaurentSeries R} {k : ℤ} {c : R} (hc : c ≠ 0)
    (hk : x.coeff k = c) (hlt : ∀ n < k, x.coeff n = 0) :
    x = single k (1 : R) * HahnSeries.ofPowerSeries ℤ R (LaurentSeries.powerSeriesPart x) ∧
      PowerSeries.constantCoeff (LaurentSeries.powerSeriesPart x) = c := by
  have hx_ne : x ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (g := k) (by rw [hk]; exact hc)
  have hord : x.order = k := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hk]; exact hc)) ?_
    by_contra h
    rw [not_le] at h
    exact hx_ne (HahnSeries.coeff_order_eq_zero.mp (hlt _ h))
  refine ⟨?_, ?_⟩
  · have h := LaurentSeries.ofPowerSeries_powerSeriesPart x
    rw [hord] at h
    rw [h, ← mul_assoc, HahnSeries.single_mul_single, mul_one, add_neg_cancel, HahnSeries.single_zero_one, one_mul]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff, hord]
    simpa using hk

theorem isUnit_natCast (q : ℕ) [Fact q.Prime] [CharP R q] (n : ℕ) (h0 : 0 < n) (hq : n < q) :
    IsUnit ((n : ℕ) : R) := by
  have hne : ((n : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod q) q n]
    exact fun h => absurd (Nat.le_of_dvd h0 h) (not_le.mpr hq)
  have h := (IsUnit.mk0 _ hne).map (ZMod.castHom (dvd_refl q) R)
  rwa [map_natCast] at h

theorem main (q : ℕ) [Fact q.Prime] [CharP R q] (hq : q ≠ 2)
    (W : WeierstrassCurve R) (x y ω : LaurentSeries R)
    (heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆)
    (hx2 : x.coeff (-2) = 1) (hx : ∀ n < -2, x.coeff n = 0)
    (hy3 : y.coeff (-3) = -1) (hy : ∀ n < -3, y.coeff n = 0)
    (hω : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative R x) :
    ω.coeff ((q : ℤ) - 1) = W.hasseInvariant q := by
  nontriviality R
  have hp : q.Prime := Fact.out
  have hq3 : 3 ≤ q := by have := hp.two_le; omega
  set m : ℕ := (q - 1) / 2 with hm
  have hqm : q - 1 = 2 * m := by obtain ⟨r, hr⟩ := hp.even_sub_one hq; omega

  have h2u : IsUnit (2 : R) := by exact_mod_cast isUnit_natCast (R := R) q 2 (by norm_num) (by omega)
  have hneg2u : IsUnit (-2 : R) := h2u.neg
  obtain ⟨d, hd⟩ : ∃ d : R, (-2) * d = 1 := hneg2u.exists_right_inv
  have hfrob : (-2 : R) ^ q = -2 := by
    have h := frobenius_def (R := R) q (-2)
    rw [map_neg, map_ofNat] at h
    exact h.symm

  set Y : LaurentSeries R := 2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃ with hYdef
  set Dx := LaurentSeries.derivative R x with hDx
  obtain ⟨hxeq, hux⟩ := eq_single_mul_powerSeriesPart (one_ne_zero) hx2 hx
  set ux := LaurentSeries.powerSeriesPart x with huxdef

  have hYlow : ∀ n < -3, Y.coeff n = 0 := by
    intro n hn
    rw [hYdef, HahnSeries.coeff_add, HahnSeries.coeff_add, show (2 : LaurentSeries R) = ((2 : ℕ) : LaurentSeries R) by norm_num,
      coeff_natCast_mul, coeff_C_mul, hy _ hn, hx _ (by omega), HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)]
    simp
  have hY3 : Y.coeff (-3) = -2 := by
    rw [hYdef, HahnSeries.coeff_add, HahnSeries.coeff_add, show (2 : LaurentSeries R) = ((2 : ℕ) : LaurentSeries R) by norm_num,
      coeff_natCast_mul, coeff_C_mul, hy3, hx _ (by omega), HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)]
    norm_num
  obtain ⟨hYeq, huY⟩ := eq_single_mul_powerSeriesPart (by rw [Ne, neg_eq_zero]; exact h2u.ne_zero) hY3 hYlow
  set uY := LaurentSeries.powerSeriesPart Y with huYdef

  set xinv : LaurentSeries R := single (2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R (ux.invOfUnit 1) with hxinv
  have huxinv : ux * ux.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit ux 1 (by rw [hux]; rfl)
  have hxxinv : x * xinv = 1 := by
    rw [hxeq, hxinv]
    calc single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R ux * (single (2 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (ux.invOfUnit 1))
        = (single (-2 : ℤ) (1 : R) * single (2 : ℤ) 1) * HahnSeries.ofPowerSeries ℤ R (ux * ux.invOfUnit 1) := by
          rw [map_mul]; ring
      _ = 1 := by rw [HahnSeries.single_mul_single, mul_one, neg_add_cancel, huxinv, RingHom.map_one, HahnSeries.single_zero_one, one_mul]
  set uYinv := uY.invOfUnit hneg2u.unit with huYinv
  have huYinv' : uY * uYinv = 1 := PowerSeries.mul_invOfUnit uY hneg2u.unit (by rw [huY]; rfl)
  have hcuYinv : PowerSeries.constantCoeff uYinv = d := by
    have h1 : PowerSeries.constantCoeff uYinv = ((hneg2u.unit⁻¹ : Rˣ) : R) := PowerSeries.constantCoeff_invOfUnit _ _
    rw [h1]
    have h2 : (-2 : R) * ((hneg2u.unit⁻¹ : Rˣ) : R) = 1 := by
      have h := Units.mul_inv hneg2u.unit
      rwa [IsUnit.unit_spec] at h
    calc ((hneg2u.unit⁻¹ : Rˣ) : R) = ((-2) * d) * ((hneg2u.unit⁻¹ : Rˣ) : R) := by rw [hd, one_mul]
      _ = d * ((-2 : R) * ((hneg2u.unit⁻¹ : Rˣ) : R)) := by ring
      _ = d := by rw [h2, mul_one]
  set Yinv : LaurentSeries R := single (3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R uYinv with hYinv
  have hYYinv : Y * Yinv = 1 := by
    rw [hYeq, hYinv]
    calc single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R uY * (single (3 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R uYinv)
        = (single (-3 : ℤ) (1 : R) * single (3 : ℤ) 1) * HahnSeries.ofPowerSeries ℤ R (uY * uYinv) := by
          rw [map_mul]; ring
      _ = 1 := by rw [HahnSeries.single_mul_single, mul_one, neg_add_cancel, huYinv', RingHom.map_one, HahnSeries.single_zero_one, one_mul]

  have hωeq : ω = Dx * Yinv := by
    calc ω = ω * (Y * Yinv) := by rw [hYYinv, mul_one]
      _ = (ω * Y) * Yinv := by ring
      _ = Dx * Yinv := by rw [hω]
  have hDxlow : ∀ n < -3, Dx.coeff n = 0 := by
    intro n hn; rw [hDx, coeff_derivative, hx _ (by omega), mul_zero]
  have hYinvlow : ∀ n < 3, Yinv.coeff n = 0 := fun n hn => single_mul_ofPowerSeries_coeff_lt _ _ hn
  have hωlow : ∀ n < 0, ω.coeff n = 0 := by
    intro n hn; rw [hωeq]; exact coeff_mul_eq_zero_of_lt hDxlow hYinvlow (by omega)

  set s : LaurentSeries R := HahnSeries.C (-2 : R) * x * Yinv with hs
  have hseq : s = single (1 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R (PowerSeries.C (-2 : R) * ux * uYinv) := by
    rw [hs, hxeq, hYinv, map_mul, map_mul, HahnSeries.ofPowerSeries_C]
    have : single (1 : ℤ) (1 : R) = single (-2 : ℤ) (1 : R) * single (3 : ℤ) 1 := by
      rw [HahnSeries.single_mul_single, mul_one]; norm_num
    rw [this]; ring
  have hs1 : s.coeff 1 = 1 := by
    rw [hseq, single_mul_ofPowerSeries_coeff_self, map_mul, map_mul, PowerSeries.constantCoeff_C, hux, hcuYinv, mul_one, hd]
  have hslow : ∀ n < 1, s.coeff n = 0 := fun n hn => by rw [hseq]; exact single_mul_ofPowerSeries_coeff_lt _ _ hn
  set v : LaurentSeries R := HahnSeries.C d * xinv ^ q * Y ^ q with hv
  have hsv : s ^ q * v = 1 := by
    rw [hs, hv, mul_pow, mul_pow, ← map_pow, hfrob]
    calc HahnSeries.C (-2 : R) * x ^ q * Yinv ^ q * (HahnSeries.C d * xinv ^ q * Y ^ q)
        = HahnSeries.C ((-2) * d) * (x * xinv) ^ q * (Y * Yinv) ^ q := by rw [map_mul]; ring
      _ = 1 := by rw [hd, map_one, hxxinv, hYYinv]; simp

  have hR4 := LaurentSeries.coeff_neg_one_mul_inv_pow_uniformizer q ω s v hωlow hs1 hslow hsv
  rw [← hR4]

  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hωv : ω * v = HahnSeries.C d * (Y ^ (q - 1) * (xinv ^ q * Dx)) := by
    rw [hωeq, hv]
    have hYq : Y ^ q = Y ^ (q - 1) * Y := by
      conv_lhs => rw [hq', pow_succ]
      rw [show q' = q - 1 by omega]
    rw [hYq]
    calc Dx * Yinv * (HahnSeries.C d * xinv ^ q * (Y ^ (q - 1) * Y))
        = HahnSeries.C d * (Y ^ (q - 1) * (xinv ^ q * Dx)) * (Y * Yinv) := by ring
      _ = HahnSeries.C d * (Y ^ (q - 1) * (xinv ^ q * Dx)) := by rw [hYYinv, mul_one]

  set f : Polynomial R := W.twoTorsionPolynomial.toPoly with hf
  have hYsq : Y ^ 2 = f.eval₂ (HahnSeries.C (Γ := ℤ) (R := R)) x := by
    rw [hf]
    simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_ofNat, map_add, map_mul, map_pow, map_ofNat]
    rw [hYdef]
    linear_combination (4 : LaurentSeries R) * heq
  have hfdeg : f.natDegree ≤ 3 := by
    rw [hf, Cubic.toPoly]; exact Polynomial.natDegree_cubic_le
  have hfmdeg : (f ^ m).natDegree < 3 * m + 1 := by
    have := Polynomial.natDegree_pow_le (p := f) (n := m)
    have h2 := Nat.mul_le_mul_left m hfdeg
    omega
  have hYpow : Y ^ (q - 1) = ∑ j ∈ Finset.range (3 * m + 1), HahnSeries.C ((f ^ m).coeff j) * x ^ j := by
    rw [hqm, pow_mul, hYsq, ← eval₂_pow]
    exact Polynomial.eval₂_eq_sum_range' (HahnSeries.C (Γ := ℤ) (R := R)) hfmdeg x

  have hres : ∀ j : ℕ, j < 3 * m + 1 → (x ^ j * (xinv ^ q * Dx)).coeff (-1) = if j = q - 1 then -2 else 0 := by
    intro j hj
    by_cases hjq : q ≤ j
    ·
      obtain ⟨n, rfl⟩ : ∃ n, j = q + n := ⟨j - q, by omega⟩
      rw [if_neg (by omega)]
      have : x ^ (q + n) * (xinv ^ q * Dx) = (x * xinv) ^ q * (x ^ n * Dx) := by ring
      rw [this, hxxinv, one_pow, one_mul]
      exact res_pow_mul_derivative x n (isUnit_natCast q _ (by omega) (by omega))
    ·
      obtain ⟨k, hk⟩ : ∃ k, q = j + k := ⟨q - j, by omega⟩
      have hk1 : 1 ≤ k := by omega
      have : x ^ j * (xinv ^ q * Dx) = (x * xinv) ^ j * (xinv ^ k * Dx) := by rw [hk]; ring
      rw [this, hxxinv, one_pow, one_mul]
      rcases eq_or_lt_of_le hk1 with h1 | h1
      ·
        rw [← h1, pow_one, if_pos (by omega)]
        have h := LaurentSeries.coeff_neg_one_inv_mul_derivative x xinv (-2) hx2 hx hxxinv
        rw [h]; norm_num
      · rw [if_neg (by omega)]
        exact res_inv_pow_mul_derivative hxxinv k (by omega) (isUnit_natCast q _ (by omega) (by omega))

  rw [hωv, hYpow, coeff_C_mul, Finset.sum_mul, coeff_finset_sum]
  have hterm : ∀ j ∈ Finset.range (3 * m + 1),
      (HahnSeries.C ((f ^ m).coeff j) * x ^ j * (xinv ^ q * Dx)).coeff (-1) =
        if j = q - 1 then (f ^ m).coeff j * (-2) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_assoc, coeff_C_mul, hres j hj]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (by rw [Finset.mem_range]; omega)]

  have hA : (f ^ m).coeff (q - 1) = W.hasseInvariant q := by
    rw [WeierstrassCurve.hasseInvariant, ← hf, ← hm]
  rw [← hA]
  linear_combination ((f ^ m).coeff (q - 1)) * hd

end WeierstrassCurve.KATZ

theorem solution
    {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q] (hq : q ≠ 2)
    (W : WeierstrassCurve R) (x y ω : LaurentSeries R)
    (heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆)
    (hx2 : x.coeff (-2) = 1) (hx : ∀ n < -2, x.coeff n = 0)
    (hy3 : y.coeff (-3) = -1) (hy : ∀ n < -3, y.coeff n = 0)
    (hω : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative R x) :
    ω.coeff ((q : ℤ) - 1) = W.hasseInvariant q :=
  WeierstrassCurve.KATZ.main q hq W x y ω heq hx2 hx hy3 hy hω

end S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant
end P2MW
export P2MW.S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant (solution)
