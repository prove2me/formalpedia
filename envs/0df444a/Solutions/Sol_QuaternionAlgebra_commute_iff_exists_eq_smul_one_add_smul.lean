-- Prove2me | solution 1 for QuaternionAlgebra.commute_iff_exists_eq_smul_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/636a3e7e-098b-5233-a9b3-2ae246bcc1bb

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul

open QuaternionAlgebra Polynomial
open scoped Quaternion

noncomputable section

namespace Q15e3

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R :=
  2 * x.re

@[scoped simp] theorem nrd_mk (x₀ x₁ x₂ x₃ : R) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 :=
  rfl

@[scoped simp] theorem trd_mk (x₀ x₁ x₂ x₃ : R) :
    trd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = 2 * x₀ :=
  rfl

@[scoped simp] theorem nrd_zero : nrd (0 : ℍ[R, a, b]) = 0 := by
  simp [nrd]

@[scoped simp] theorem nrd_one : nrd (1 : ℍ[R, a, b]) = 1 := by
  simp [nrd]

@[scoped simp] theorem nrd_neg (x : ℍ[R, a, b]) : nrd (-x) = nrd x := by
  simp [nrd]

@[scoped simp] theorem nrd_star (x : ℍ[R, a, b]) : nrd (star x) = nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [star_mk, nrd_mk]
  ring

@[scoped simp] theorem nrd_coe (r : R) : nrd ((r : R) : ℍ[R, a, b]) = r ^ 2 := by
  simp [nrd]

theorem mul_star_eq_coe_nrd (x : ℍ[R, a, b]) :
    x * star x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;>
    simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;>
    ring

theorem star_mul_eq_coe_nrd (x : ℍ[R, a, b]) :
    star x * x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;>
    simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;>
    ring

theorem add_star_eq_coe_trd (x : ℍ[R, a, b]) :
    x + star x = ((trd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;>
    simp only [star_mk, mk_add_mk, trd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;>
    ring

theorem nrd_mul (x y : ℍ[R, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk, nrd_mk]
  ring

theorem sq_sub_trd_mul_add_nrd (x : ℍ[R, a, b]) :
    x * x - ((trd x : R) : ℍ[R, a, b]) * x + ((nrd x : R) : ℍ[R, a, b]) = 0 := by
  have h1 : ((trd x : R) : ℍ[R, a, b]) = x + star x := (add_star_eq_coe_trd x).symm
  have h2 : ((nrd x : R) : ℍ[R, a, b]) = star x * x := (star_mul_eq_coe_nrd x).symm
  rw [h1, h2, add_mul]
  abel

end ReducedNorm

section Definite

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b : K}

theorem nrd_nonneg (ha : a < 0) (hb : b < 0) (x : ℍ[K, a, b]) : 0 ≤ nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have h1 : (0 : K) ≤ x₀ ^ 2 := sq_nonneg _
  have h2 : (0 : K) ≤ (-a) * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : (0 : K) ≤ (-b) * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : (0 : K) ≤ (a * b) * x₃ ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  simp only [nrd_mk]
  nlinarith

theorem nrd_ne_zero_of_ne_zero (ha : a < 0) (hb : b < 0) {x : ℍ[K, a, b]} (hx : x ≠ 0) :
    nrd x ≠ 0 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x

  intro h
  apply hx
  have h1 : (0 : K) ≤ x₀ ^ 2 := sq_nonneg _
  have h2 : (0 : K) ≤ (-a) * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : (0 : K) ≤ (-b) * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : (0 : K) ≤ (a * b) * x₃ ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  simp only [nrd_mk] at h
  have e0 : x₀ ^ 2 = 0 := by nlinarith
  have e1 : (-a) * x₁ ^ 2 = 0 := by nlinarith
  have e2 : (-b) * x₂ ^ 2 = 0 := by nlinarith
  have e3 : (a * b) * x₃ ^ 2 = 0 := by nlinarith
  have ha' : (-a) ≠ 0 := by linarith
  have hb' : (-b) ≠ 0 := by linarith
  have hab : a * b ≠ 0 := mul_ne_zero ha.ne hb.ne
  ext
  · exact (pow_eq_zero_iff (by norm_num)).mp e0
  · exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp e1).resolve_left ha')
  · exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp e2).resolve_left hb')
  · exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp e3).resolve_left hab)

theorem isUnit_of_ne_zero (ha : a < 0) (hb : b < 0) {x : ℍ[K, a, b]} (hx : x ≠ 0) :
    IsUnit x := by
  have hn : nrd x ≠ 0 := nrd_ne_zero_of_ne_zero ha hb hx
  refine ⟨⟨x, ((nrd x)⁻¹ : K) • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, mul_star_eq_coe_nrd, ← coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
      inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]
  · rw [smul_mul_assoc, star_mul_eq_coe_nrd, ← coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
      inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]

end Definite

section IsIntegerRat

def IsIntegerRat (r : ℚ) : Prop :=
  ∃ n : ℤ, (n : ℚ) = r

@[scoped simp] theorem isIntegerRat_intCast (n : ℤ) : IsIntegerRat (n : ℚ) :=
  ⟨n, rfl⟩

@[scoped simp] theorem isIntegerRat_zero : IsIntegerRat (0 : ℚ) :=
  ⟨0, by norm_num⟩

@[scoped simp] theorem isIntegerRat_one : IsIntegerRat (1 : ℚ) :=
  ⟨1, by norm_num⟩

theorem IsIntegerRat.add {r s : ℚ} (hr : IsIntegerRat r) (hs : IsIntegerRat s) :
    IsIntegerRat (r + s) := by
  obtain ⟨m, hm⟩ := hr
  obtain ⟨n, hn⟩ := hs
  exact ⟨m + n, by push_cast [hm, hn]; ring⟩

theorem IsIntegerRat.neg {r : ℚ} (hr : IsIntegerRat r) : IsIntegerRat (-r) := by
  obtain ⟨m, hm⟩ := hr
  exact ⟨-m, by push_cast [hm]; ring⟩

theorem IsIntegerRat.sub {r s : ℚ} (hr : IsIntegerRat r) (hs : IsIntegerRat s) :
    IsIntegerRat (r - s) := by
  obtain ⟨m, hm⟩ := hr
  obtain ⟨n, hn⟩ := hs
  exact ⟨m - n, by push_cast [hm, hn]; ring⟩

theorem IsIntegerRat.mul {r s : ℚ} (hr : IsIntegerRat r) (hs : IsIntegerRat s) :
    IsIntegerRat (r * s) := by
  obtain ⟨m, hm⟩ := hr
  obtain ⟨n, hn⟩ := hs
  exact ⟨m * n, by push_cast [hm, hn]; ring⟩

theorem IsIntegerRat.congr {r s : ℚ} (hr : IsIntegerRat r) (h : r = s) : IsIntegerRat s :=
  h ▸ hr

theorem not_isIntegerRat_of_two_mul_eq_odd {r : ℚ} (k : ℤ) (hk : k % 2 = 1)
    (h : 2 * r = (k : ℚ)) : ¬ IsIntegerRat r := by
  rintro ⟨n, hn⟩
  rw [← hn] at h
  have h2 : ((2 * n : ℤ) : ℚ) = (k : ℚ) := by push_cast; linarith
  have h3 : (2 * n : ℤ) = k := by exact_mod_cast h2
  omega

theorem not_isIntegerRat_half : ¬ IsIntegerRat (1 / 2 : ℚ) :=
  not_isIntegerRat_of_two_mul_eq_odd 1 rfl (by norm_num)

end IsIntegerRat

section Projections

variable {a b : ℚ}

@[scoped simp] theorem add_re' (x y : ℍ[ℚ, a, b]) : (x + y).re = x.re + y.re := rfl
@[scoped simp] theorem add_imI' (x y : ℍ[ℚ, a, b]) : (x + y).imI = x.imI + y.imI := rfl
@[scoped simp] theorem add_imJ' (x y : ℍ[ℚ, a, b]) : (x + y).imJ = x.imJ + y.imJ := rfl
@[scoped simp] theorem add_imK' (x y : ℍ[ℚ, a, b]) : (x + y).imK = x.imK + y.imK := rfl

@[scoped simp] theorem neg_re' (x : ℍ[ℚ, a, b]) : (-x).re = -x.re := rfl
@[scoped simp] theorem neg_imI' (x : ℍ[ℚ, a, b]) : (-x).imI = -x.imI := rfl
@[scoped simp] theorem neg_imJ' (x : ℍ[ℚ, a, b]) : (-x).imJ = -x.imJ := rfl
@[scoped simp] theorem neg_imK' (x : ℍ[ℚ, a, b]) : (-x).imK = -x.imK := rfl

@[scoped simp] theorem ratsmul_re' (c : ℚ) (x : ℍ[ℚ, a, b]) : (c • x).re = c * x.re := rfl
@[scoped simp] theorem ratsmul_imI' (c : ℚ) (x : ℍ[ℚ, a, b]) : (c • x).imI = c * x.imI := rfl
@[scoped simp] theorem ratsmul_imJ' (c : ℚ) (x : ℍ[ℚ, a, b]) : (c • x).imJ = c * x.imJ := rfl
@[scoped simp] theorem ratsmul_imK' (c : ℚ) (x : ℍ[ℚ, a, b]) : (c • x).imK = c * x.imK := rfl

theorem mul_re' (x y : ℍ[ℚ, a, b]) :
    (x * y).re = x.re * y.re + a * (x.imI * y.imI) + b * (x.imJ * y.imJ)
      - a * b * (x.imK * y.imK) := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [mk_mul_mk]
  ring

theorem mul_imI' (x y : ℍ[ℚ, a, b]) :
    (x * y).imI = x.re * y.imI + x.imI * y.re - b * (x.imJ * y.imK) + b * (x.imK * y.imJ) := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [mk_mul_mk]
  ring

theorem mul_imJ' (x y : ℍ[ℚ, a, b]) :
    (x * y).imJ = x.re * y.imJ + a * (x.imI * y.imK) + x.imJ * y.re
      - a * (x.imK * y.imI) := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [mk_mul_mk]
  ring

theorem mul_imK' (x y : ℍ[ℚ, a, b]) :
    (x * y).imK = x.re * y.imK + x.imI * y.imJ - x.imJ * y.imI + x.imK * y.re := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [mk_mul_mk]
  ring

theorem trd_eq (x : ℍ[ℚ, a, b]) : trd x = 2 * x.re := rfl

theorem nrd_eq (x : ℍ[ℚ, a, b]) :
    nrd x = x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 := rfl

theorem one_re' : (1 : ℍ[ℚ, a, b]).re = 1 := rfl
theorem one_imI' : (1 : ℍ[ℚ, a, b]).imI = 0 := rfl
theorem one_imJ' : (1 : ℍ[ℚ, a, b]).imJ = 0 := rfl
theorem one_imK' : (1 : ℍ[ℚ, a, b]).imK = 0 := rfl

end Projections

section IsOrderLemmas
variable {a b : ℚ}

theorem isOrder_intCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsOrder Λ) (n : ℤ) :
    ((n : ℤ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have key : ((n : ℤ) : ℍ[ℚ, a, b]) = n • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]
  rw [key]
  exact Λ.smul_mem n h.one_mem

def basisI (a b : ℚ) : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩

def basisJ (a b : ℚ) : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
end IsOrderLemmas

section Integrality
variable {a b : ℚ}

variable {a b : ℚ}

def cd123m5_hom_orderSubalgebra {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsOrder Λ) :
    Subalgebra ℤ ℍ[ℚ, a, b] where
  carrier := (Λ : Set ℍ[ℚ, a, b])
  mul_mem' := fun hx hy => h.mul_mem hx hy
  one_mem' := h.one_mem
  add_mem' := fun hx hy => Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  algebraMap_mem' := fun n => by
    rw [eq_intCast (algebraMap ℤ ℍ[ℚ, a, b]) n]
    exact isOrder_intCast_mem h n

theorem cd123m5_hom_orderSubalgebra_toSubmodule {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (h : IsOrder Λ) : Subalgebra.toSubmodule (cd123m5_hom_orderSubalgebra h) = Λ := by
  ext y
  exact Iff.rfl

theorem cd123m5_hom_isIntegral_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : IsIntegral ℤ x :=
  IsIntegral.of_mem_of_fg (cd123m5_hom_orderSubalgebra h)
    (by rw [cd123m5_hom_orderSubalgebra_toSubmodule h]; exact h.fg) x hx

theorem cd123m5_hom_isIntegerRat_re_of_isIntegral_central {x : ℍ[ℚ, a, b]}
    (hx : IsIntegral ℤ x) (hI : x.imI = 0) (hJ : x.imJ = 0) (hK : x.imK = 0) :
    IsIntegerRat x.re := by
  obtain ⟨p, hpm, hp0⟩ := hx
  have hp0' : (Polynomial.aeval x) p = 0 := by
    rw [Polynomial.aeval_def]; exact hp0
  have hxre : x = algebraMap ℚ ℍ[ℚ, a, b] x.re := by
    rw [coe_algebraMap]
    ext <;> simp [hI, hJ, hK]
  have h1 := Polynomial.aeval_algebraMap_apply ℍ[ℚ, a, b] x.re p
  rw [← hxre, hp0'] at h1
  have hinj : Function.Injective (algebraMap ℚ ℍ[ℚ, a, b]) := by
    rw [coe_algebraMap]; exact coe_injective
  have h2 : (Polynomial.aeval x.re) p = 0 := by
    apply hinj
    rw [map_zero]
    exact h1.symm
  have hint : IsIntegral ℤ x.re := ⟨p, hpm, by rw [← Polynomial.aeval_def]; exact h2⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨n, by rwa [eq_intCast (algebraMap ℤ ℚ) n] at hn⟩

theorem cd123m5_hom_trd_nrd_isIntegerRat_of_isIntegral {x : ℍ[ℚ, a, b]}
    (hx : IsIntegral ℤ x) : IsIntegerRat (trd x) ∧ IsIntegerRat (nrd x) := by
  by_cases hcen : x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · obtain ⟨hI, hJ, hK⟩ := hcen
    obtain ⟨m, hm⟩ := cd123m5_hom_isIntegerRat_re_of_isIntegral_central hx hI hJ hK
    constructor
    · exact ⟨2 * m, by rw [trd_eq, ← hm]; push_cast; ring⟩
    · exact ⟨m ^ 2, by rw [nrd_eq, hI, hJ, hK, ← hm]; push_cast; ring⟩
  · obtain ⟨p, hpm, hp0⟩ := hx
    have hp0' : (Polynomial.aeval x) p = 0 := by
      rw [Polynomial.aeval_def]; exact hp0

    set f : ℚ[X] := X ^ 2 + (C (-(trd x)) * X + C (nrd x)) with hfdef
    have hfm : f.Monic := by
      rw [hfdef]
      exact monic_X_pow_add (lt_of_le_of_lt degree_linear_le
        (by exact_mod_cast Nat.one_lt_two))
    have hfdeg : f.degree = ((2 : ℕ) : WithBot ℕ) := by
      have h1 : (C (-(trd x)) * X + C (nrd x)).degree < ((X : ℚ[X]) ^ 2).degree := by
        rw [degree_X_pow]
        exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast Nat.one_lt_two)
      rw [hfdef, degree_add_eq_left_of_degree_lt h1, degree_X_pow]
    have hfx : (Polynomial.aeval x) f = 0 := by
      rw [hfdef]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, map_neg]
      rw [coe_algebraMap]
      rw [pow_two, neg_mul, ← add_assoc, ← sub_eq_add_neg]
      exact sq_sub_trd_mul_add_nrd x

    set q : ℚ[X] := p.map (algebraMap ℤ ℚ) with hqdef
    have hqx : (Polynomial.aeval x) q = 0 := by
      rw [hqdef, Polynomial.aeval_map_algebraMap]
      exact hp0'

    have hrx : (Polynomial.aeval x) (q %ₘ f) = 0 := by
      have hdiv := Polynomial.modByMonic_add_div q f
      have := congrArg (Polynomial.aeval x) hdiv
      rw [map_add, map_mul, hfx, zero_mul, add_zero, hqx] at this
      exact this
    have hrdeg : (q %ₘ f).degree ≤ 1 := by
      have hlt := Polynomial.degree_modByMonic_lt q hfm
      rw [hfdeg] at hlt
      by_cases hz : q %ₘ f = 0
      · rw [hz, Polynomial.degree_zero]
        exact bot_le
      · rw [Polynomial.degree_eq_natDegree hz] at hlt ⊢
        have h2 : (q %ₘ f).natDegree < 2 := by exact_mod_cast hlt
        exact_mod_cast Nat.lt_succ_iff.mp h2
    have hform := Polynomial.eq_X_add_C_of_degree_le_one hrdeg
    set c : ℚ := (q %ₘ f).coeff 1 with hcdef
    set d : ℚ := (q %ₘ f).coeff 0 with hddef
    rw [hform] at hrx
    simp only [map_add, map_mul, aeval_X, aeval_C] at hrx
    rw [coe_algebraMap] at hrx
    have h1 : c * x.imI = 0 := by
      have := congrArg QuaternionAlgebra.imI hrx
      simpa [mul_imI', QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe,
        QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe] using this
    have h2 : c * x.imJ = 0 := by
      have := congrArg QuaternionAlgebra.imJ hrx
      simpa [mul_imJ', QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe,
        QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe] using this
    have h3 : c * x.imK = 0 := by
      have := congrArg QuaternionAlgebra.imK hrx
      simpa [mul_imK', QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe,
        QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe] using this
    have hRe : c * x.re + d = 0 := by
      have := congrArg QuaternionAlgebra.re hrx
      simpa [mul_re', QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe,
        QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe] using this
    have hcz : c = 0 := by
      by_contra hcne
      exact hcen ⟨(mul_eq_zero.mp h1).resolve_left hcne,
        (mul_eq_zero.mp h2).resolve_left hcne,
        (mul_eq_zero.mp h3).resolve_left hcne⟩
    have hdz : d = 0 := by
      rw [hcz, zero_mul, zero_add] at hRe
      exact hRe
    have hr0 : q %ₘ f = 0 := by
      rw [hform, hcz, hdz, map_zero, zero_mul, zero_add]

    have hdvd : f ∣ p.map (algebraMap ℤ ℚ) := by
      refine ⟨q /ₘ f, ?_⟩
      have hdiv := Polynomial.modByMonic_add_div q f
      rw [hr0, zero_add] at hdiv
      exact hdiv.symm
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hpm hdvd
    rw [hfm.leadingCoeff, Polynomial.C_1, mul_one] at hg
    have hc1 : ((g.coeff 1 : ℤ) : ℚ) = -(trd x) := by
      have hco := congrArg (fun P : ℚ[X] => P.coeff 1) hg
      simp only [Polynomial.coeff_map, hfdef, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
        Polynomial.coeff_C] at hco
      rw [eq_intCast (algebraMap ℤ ℚ) (g.coeff 1)] at hco
      norm_num at hco
      exact hco
    have hc0 : ((g.coeff 0 : ℤ) : ℚ) = nrd x := by
      have hco := congrArg (fun P : ℚ[X] => P.coeff 0) hg
      simp only [Polynomial.coeff_map, hfdef, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, mul_zero,
        Polynomial.coeff_C] at hco
      rw [eq_intCast (algebraMap ℤ ℚ) (g.coeff 0)] at hco
      norm_num at hco
      exact hco
    refine ⟨⟨-(g.coeff 1), ?_⟩, ⟨g.coeff 0, hc0⟩⟩
    push_cast
    rw [hc1, neg_neg]

theorem cd123m5_hom_trd_isIntegerRat_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : IsIntegerRat (trd x) :=
  (cd123m5_hom_trd_nrd_isIntegerRat_of_isIntegral (cd123m5_hom_isIntegral_of_mem h hx)).1

theorem cd123m5_hom_nrd_isIntegerRat_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : IsIntegerRat (nrd x) :=
  (cd123m5_hom_trd_nrd_isIntegerRat_of_isIntegral (cd123m5_hom_isIntegral_of_mem h hx)).2

end Integrality

section P2Range
variable {a b : ℚ}

theorem kw_surge_e17l3p2_nrd_smul (r : ℚ) (x : ℍ[ℚ, a, b]) :
    nrd (r • x) = r ^ 2 * nrd x := by
  obtain ⟨w, i, j, k⟩ := x
  rw [QuaternionAlgebra.smul_mk, nrd_mk, nrd_mk]
  simp only [smul_eq_mul]; ring

theorem kw_surge_e17l3p2_scalar_mem_int {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (htrd : ∀ x ∈ Λ, IsIntegerRat (trd x)) (hnrd : ∀ x ∈ Λ, IsIntegerRat (nrd x))
    {c : ℚ} (hc : c • (1 : ℍ[ℚ, a, b]) ∈ Λ) : ∃ m : ℤ, c = (m : ℚ) := by
  obtain ⟨T, hT⟩ := htrd _ hc
  obtain ⟨N, hN⟩ := hnrd _ hc
  have htc : 2 * c = (T : ℚ) := by
    have h1 : trd (c • (1:ℍ[ℚ,a,b])) = 2 * c := by
      rw [trd_eq, show ((1:ℍ[ℚ,a,b]) = ⟨1,0,0,0⟩) from rfl,
        QuaternionAlgebra.smul_mk]; simp [smul_eq_mul]
    linarith [hT.trans h1]
  have hnc : c ^ 2 = (N : ℚ) := by
    have h1 : nrd (c • (1:ℍ[ℚ,a,b])) = c ^ 2 := by
      rw [kw_surge_e17l3p2_nrd_smul, nrd_one, mul_one]
    linarith [hN.trans h1]
  have hT2Z : T ^ 2 = 4 * N := by
    have hT2 : (T : ℚ) ^ 2 = 4 * (N : ℚ) := by
      have : (T : ℚ) = 2 * c := htc.symm
      rw [this]; linarith [hnc]
    exact_mod_cast hT2
  have hTeven : 2 ∣ T := by
    rcases Int.even_or_odd T with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨s, by omega⟩
    · exfalso
      have hsq : T ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by rw [hs]; ring
      omega
  obtain ⟨m, hm⟩ := hTeven
  refine ⟨m, ?_⟩
  have hTm : (T:ℚ) = 2 * (m:ℚ) := by exact_mod_cast hm
  linarith

theorem kw_surge_e17l3p2_qLinComb_inj {α : ℍ[ℚ, a, b]}
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) {c e c' e' : ℚ}
    (h : c • (1:ℍ[ℚ,a,b]) + e • α = c' • (1:ℍ[ℚ,a,b]) + e' • α) :
    c = c' ∧ e = e' := by
  obtain ⟨r, i, j, k⟩ := α
  simp only at hnc
  rw [show ((1 : ℍ[ℚ,a,b]) = ⟨1,0,0,0⟩) from rfl,
    QuaternionAlgebra.smul_mk, QuaternionAlgebra.smul_mk,
    QuaternionAlgebra.smul_mk, QuaternionAlgebra.smul_mk,
    show (∀ w x y z w' x' y' z' : ℚ,
      (⟨w,x,y,z⟩ : ℍ[ℚ,a,b]) + ⟨w',x',y',z'⟩ = ⟨w+w',x+x',y+y',z+z'⟩)
      from fun _ _ _ _ _ _ _ _ => rfl,
    show (∀ w x y z w' x' y' z' : ℚ,
      (⟨w,x,y,z⟩ : ℍ[ℚ,a,b]) + ⟨w',x',y',z'⟩ = ⟨w+w',x+x',y+y',z+z'⟩)
      from fun _ _ _ _ _ _ _ _ => rfl,
    QuaternionAlgebra.mk.injEq] at h
  simp only [smul_eq_mul, mul_one, mul_zero, zero_add] at h
  obtain ⟨hre, hI, hJ, hK⟩ := h
  simp only [not_and_or] at hnc
  have hee : e = e' := by
    rcases hnc with hi | hj | hk
    · exact mul_right_cancel₀ hi hI
    · exact mul_right_cancel₀ hj hJ
    · exact mul_right_cancel₀ hk hK
  rw [hee] at hre
  exact ⟨by linarith, hee⟩

end P2Range

section ConductorPred
variable {a b : ℚ}

def kw_surge_e17l3co_condStepPred (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (g : ℕ) : Prop :=
  ∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
    ∃ p q : ℤ, (g : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α

def kw_surge_e17l3co_hasConductorPred (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) : Prop :=
  kw_surge_e17l3co_condStepPred Λ α f ∧
    ∀ g : ℕ, 0 < g → g < f → ¬ kw_surge_e17l3co_condStepPred Λ α g

theorem hasEmbeddingConductor_iff_pred (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) :
    QuaternionAlgebra.HasEmbeddingConductor Λ α f ↔ kw_surge_e17l3co_hasConductorPred Λ α f :=
  Iff.rfl
end ConductorPred

section SkolemNoether

variable {a b : ℚ}

theorem kw_ccr25a5_sn_intertwine {t n : ℤ} {α α' : ℍ[ℚ, a, b]} (hα : IsQuadraticDatum t n α)
    (hα' : IsQuadraticDatum t n α') (x : ℍ[ℚ, a, b]) :
    α * (α * x + x * α' - (t : ℚ) • x) = (α * x + x * α' - (t : ℚ) • x) * α' := by
  have h1 : α * α = (t : ℚ) • α - (n : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    rw [isQuadraticDatum_iff] at hα; rw [← sub_eq_zero, ← hα]; abel
  have h2 : α' * α' = (t : ℚ) • α' - (n : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    rw [isQuadraticDatum_iff] at hα'; rw [← sub_eq_zero, ← hα']; abel
  have e1 : α * (α * x) = (t : ℚ) • (α * x) - (n : ℚ) • x := by
    rw [← mul_assoc, h1, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have e2 : x * α' * α' = (t : ℚ) • (x * α') - (n : ℚ) • x := by
    rw [mul_assoc, h2, mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
  rw [mul_sub, mul_add, e1, mul_smul_comm, sub_mul, add_mul, e2, smul_mul_assoc,
    mul_assoc α x α']
  abel

theorem kw_ccr25a5_sn_witness {t : ℤ} {α α' : ℍ[ℚ, a, b]} (ha : a ≠ 0)
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) :
    (α * 1 + 1 * α' - (t : ℚ) • (1 : ℍ[ℚ, a, b])) ≠ 0 ∨
      (α * basisI a b + basisI a b * α' - (t : ℚ) • basisI a b) ≠ 0 ∨
      (α * basisJ a b + basisJ a b * α' - (t : ℚ) • basisJ a b) ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h1, hi, hj⟩ := h
  have hα' : α' = (t : ℚ) • (1 : ℍ[ℚ, a, b]) - α := by
    rw [mul_one, one_mul] at h1
    rw [← sub_eq_zero, ← h1]; abel
  rw [hα'] at hi hj
  apply hnc
  have e1 := congrArg QuaternionAlgebra.imJ hi
  have e2 := congrArg QuaternionAlgebra.imK hi
  have e4 := congrArg QuaternionAlgebra.imK hj
  simp [basisI, basisJ] at e1 e2 e4
  have hK : α.imK = 0 := by
    rcases e1 with h | h
    · exact absurd h ha
    · linarith
  have hJ : α.imJ = 0 := by linarith
  have hI : α.imI = 0 := by linarith
  exact ⟨hI, hJ, hK⟩

theorem kw_ccr25a5_skolemNoether (ha : a < 0) (hb : b < 0) {t n : ℤ} {α α' : ℍ[ℚ, a, b]}
    (hα : IsQuadraticDatum t n α) (hα' : IsQuadraticDatum t n α')
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) :
    ∃ g : ℍ[ℚ, a, b]ˣ, (((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b]) * α * (g : ℍ[ℚ, a, b]) = α' := by
  have key : ∀ x : ℍ[ℚ, a, b], (α * x + x * α' - (t : ℚ) • x) ≠ 0 →
      ∃ g : ℍ[ℚ, a, b]ˣ, (((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b]) * α * (g : ℍ[ℚ, a, b]) = α' := by
    intro x hx
    have hu : IsUnit (α * x + x * α' - (t : ℚ) • x) := isUnit_of_ne_zero ha hb hx
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, mul_assoc, kw_ccr25a5_sn_intertwine hα hα' x, ← mul_assoc,
      IsUnit.val_inv_mul, one_mul]
  rcases kw_ccr25a5_sn_witness (t := t) (α' := α') ha.ne hnc with h | h | h
  · exact key 1 h
  · exact key _ h
  · exact key _ h

end SkolemNoether

section Uniqueness

variable {a b : ℚ}

theorem kw_ccr25a5_int_of_ratsmul_one_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {c : ℚ}
    (hc : c • (1 : ℍ[ℚ, a, b]) ∈ R) : ∃ k : ℤ, (k : ℚ) = c := by
  obtain ⟨m, hm⟩ := kw_surge_e17l3p2_scalar_mem_int
    (fun _ hx => cd123m5_hom_trd_isIntegerRat_of_mem hR hx)
    (fun _ hx => cd123m5_hom_nrd_isIntegerRat_of_mem hR hx) hc
  exact ⟨m, hm.symm⟩

theorem kw_ccr25a5_plane_smul (r c e : ℚ) (α : ℍ[ℚ, a, b]) :
    r • (c • (1 : ℍ[ℚ, a, b]) + e • α) = (r * c) • (1 : ℍ[ℚ, a, b]) + (r * e) • α := by
  rw [smul_add, smul_smul, smul_smul]

theorem kw_ccr25a5_coeffs_int_of_condStep {R : Submodule ℤ ℍ[ℚ, a, b]} {α : ℍ[ℚ, a, b]}
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) {f : ℕ}
    (hstep : kw_surge_e17l3co_condStepPred R α f) {c e : ℚ}
    (hx : c • (1 : ℍ[ℚ, a, b]) + e • α ∈ R) :
    ∃ p q : ℤ, (p : ℚ) = f * c ∧ (q : ℚ) = f * e := by
  obtain ⟨p, q, hpq⟩ := hstep _ hx ⟨c, e, rfl⟩
  rw [kw_ccr25a5_plane_smul] at hpq
  obtain ⟨h1, h2⟩ := kw_surge_e17l3p2_qLinComb_inj hnc hpq
  exact ⟨p, q, h1.symm, h2.symm⟩

def kw_ccr25a5_numeratorIdeal (R : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) : Ideal ℤ where
  carrier := {q : ℤ | ∃ c : ℚ, c • (1 : ℍ[ℚ, a, b]) + ((q : ℚ) / (f : ℚ)) • α ∈ R}
  add_mem' := by
    rintro q q' ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c + c', ?_⟩
    convert R.add_mem hc hc' using 1
    push_cast
    rw [add_div, add_smul, add_smul]
    abel
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro k q ⟨c, hc⟩
    refine ⟨k * c, ?_⟩
    convert R.smul_mem k hc using 1
    rw [← Int.cast_smul_eq_zsmul ℚ k (c • (1 : ℍ[ℚ, a, b]) + _), kw_ccr25a5_plane_smul, smul_eq_mul,
      Int.cast_mul, mul_div_assoc]

theorem kw_ccr25a5_mem_numeratorIdeal_iff {R : Submodule ℤ ℍ[ℚ, a, b]} {α : ℍ[ℚ, a, b]} {f : ℕ} (q : ℤ) :
    q ∈ kw_ccr25a5_numeratorIdeal R α f
      ↔ ∃ c : ℚ, c • (1 : ℍ[ℚ, a, b]) + ((q : ℚ) / (f : ℚ)) • α ∈ R :=
  Iff.rfl

theorem kw_ccr25a5_mem_numeratorIdeal_of_mem {R : Submodule ℤ ℍ[ℚ, a, b]} {α : ℍ[ℚ, a, b]} {f : ℕ}
    (hf : 0 < f) {c e : ℚ} (hx : c • (1 : ℍ[ℚ, a, b]) + e • α ∈ R) {q : ℤ} (hq : (q : ℚ) = f * e) :
    q ∈ kw_ccr25a5_numeratorIdeal R α f := by
  have hf0 : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  refine ⟨c, ?_⟩
  rwa [hq, mul_div_cancel_left₀ _ hf0]

theorem kw_ccr25a5_exists_generator {R : Submodule ℤ ℍ[ℚ, a, b]}
    (hR : IsOrder R) {α : ℍ[ℚ, a, b]} (hαR : α ∈ R) (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0))
    {f : ℕ} (hf : 0 < f) (hc : kw_surge_e17l3co_hasConductorPred R α f) :
    ∃ m : ℤ, (1 / (f : ℚ)) • ((m : ℚ) • (1 : ℍ[ℚ, a, b]) + α) ∈ R := by
  have hf0 : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  set I := kw_ccr25a5_numeratorIdeal R α f with hI
  have hfI : (f : ℤ) ∈ I :=
    kw_ccr25a5_mem_numeratorIdeal_of_mem (c := 0) (e := 1) hf
      (by rw [zero_smul, zero_add, one_smul]; exact hαR) (by push_cast; ring)
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  set g' : ℕ := g.natAbs with hg'
  have hmem : ∀ q : ℤ, q ∈ I ↔ (g' : ℤ) ∣ q := fun q => by
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton, hg', Int.natAbs_dvd]
  have hg'f : g' ∣ f := by
    have := (hmem _).mp hfI
    exact_mod_cast this
  obtain ⟨f', hff'⟩ := hg'f
  have hf'pos : 0 < f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'; omega
    · exact h
  have hg'pos : 0 < g' := by
    rcases Nat.eq_zero_or_pos g' with h | h
    · rw [h, zero_mul] at hff'; omega
    · exact h

  have hstep' : kw_surge_e17l3co_condStepPred R α f' := by
    rintro x hxR ⟨c, e, rfl⟩
    obtain ⟨p, q, hp, hq⟩ := kw_ccr25a5_coeffs_int_of_condStep hnc hc.1 hxR
    obtain ⟨k, hk⟩ := (hmem q).mp (kw_ccr25a5_mem_numeratorIdeal_of_mem hf hxR hq)
    have hke : (k : ℚ) = f' * e := by
      have h1 : ((g' : ℤ) : ℚ) * k = (g' : ℚ) * (f' * e) := by
        rw [← Int.cast_mul, ← hk, hq, hff']; push_cast; ring
      have hg'0 : ((g' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg'pos.ne'
      exact mul_left_cancel₀ hg'0 (by rw [h1]; push_cast; ring)
    have hy : ((f' : ℚ) * c) • (1 : ℍ[ℚ, a, b]) ∈ R := by
      have h1 : ((f' : ℚ) * c) • (1 : ℍ[ℚ, a, b])
          = (f' : ℚ) • (c • (1 : ℍ[ℚ, a, b]) + e • α) - (k : ℚ) • α := by
        rw [kw_ccr25a5_plane_smul, hke, add_sub_cancel_right]
      rw [h1, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
      exact R.sub_mem (R.smul_of_tower_mem f' hxR) (R.smul_mem k hαR)
    obtain ⟨p', hp'⟩ := kw_ccr25a5_int_of_ratsmul_one_mem hR hy
    exact ⟨p', k, by rw [kw_ccr25a5_plane_smul, hp', hke]⟩

  have hg'1 : g' = 1 := by
    by_contra hne
    have hlt : f' < f := by
      rw [hff']
      have : 2 ≤ g' := by omega
      nlinarith
    exact hc.2 f' hf'pos hlt hstep'
  obtain ⟨c, hc1⟩ := (hmem 1).mpr (by rw [hg'1]; exact one_dvd _)
  obtain ⟨p, q, hp, -⟩ := kw_ccr25a5_coeffs_int_of_condStep hnc hc.1 hc1
  refine ⟨p, ?_⟩
  convert hc1 using 1
  rw [smul_add, smul_smul, hp, Int.cast_one, one_div, inv_mul_cancel_left₀ hf0]

theorem kw_ccr25a5_trd_plane (c e : ℚ) (α : ℍ[ℚ, a, b]) :
    trd (c • (1 : ℍ[ℚ, a, b]) + e • α) = 2 * c + e * trd α := by
  simp [trd_eq]; ring

theorem kw_ccr25a5_nrd_plane (c e : ℚ) (α : ℍ[ℚ, a, b]) :
    nrd (c • (1 : ℍ[ℚ, a, b]) + e • α) = c ^ 2 + c * e * trd α + e ^ 2 * nrd α := by
  simp [nrd_eq, trd_eq]; ring

theorem kw_ccr25a5_parity_core {f T N m₁ m₂ u₁ u₂ k₁ k₂ : ℤ} (hf : f ≠ 0)
    (hu₁ : f * u₁ = 2 * m₁ + T) (hu₂ : f * u₂ = 2 * m₂ + T)
    (hk₁ : f ^ 2 * k₁ = m₁ ^ 2 + m₁ * T + N) (hk₂ : f ^ 2 * k₂ = m₂ ^ 2 + m₂ * T + N) :
    ∃ w : ℤ, m₁ - m₂ = f * w := by
  have e₁ : (f * u₁) ^ 2 = 4 * (f ^ 2 * k₁) + (T ^ 2 - 4 * N) := by rw [hu₁, hk₁]; ring
  have e₂ : (f * u₂) ^ 2 = 4 * (f ^ 2 * k₂) + (T ^ 2 - 4 * N) := by rw [hu₂, hk₂]; ring
  have hdiff : f ^ 2 * (u₁ ^ 2 - u₂ ^ 2) = f ^ 2 * (4 * (k₁ - k₂)) := by
    linear_combination e₁ - e₂
  have hd := mul_left_cancel₀ (pow_ne_zero 2 hf) hdiff
  have hev : Even (u₁ ^ 2 - u₂ ^ 2) := ⟨2 * (k₁ - k₂), by rw [hd]; ring⟩
  rw [Int.even_sub, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero, ← Int.even_sub] at hev
  obtain ⟨w, hw⟩ := hev
  refine ⟨w, ?_⟩
  have h2 : (2 : ℤ) * (m₁ - m₂) = 2 * (f * w) := by
    have : f * (u₁ - u₂) = 2 * m₁ + T - (2 * m₂ + T) := by rw [mul_sub, hu₁, hu₂]
    rw [hw] at this
    linear_combination -this
  exact mul_left_cancel₀ two_ne_zero h2

theorem kw_ccr25a5_generator_int_eqs {R : Submodule ℤ ℍ[ℚ, a, b]}
    (hR : IsOrder R) {α : ℍ[ℚ, a, b]} {T N : ℤ} (hT : (T : ℚ) = trd α) (hN : (N : ℚ) = nrd α)
    {f : ℕ} (hf : 0 < f) {m : ℤ} (hm : (1 / (f : ℚ)) • ((m : ℚ) • (1 : ℍ[ℚ, a, b]) + α) ∈ R) :
    ∃ u k : ℤ, (f : ℤ) * u = 2 * m + T ∧ (f : ℤ) ^ 2 * k = m ^ 2 + m * T + N := by
  have hf0 : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  obtain ⟨u, hu⟩ := cd123m5_hom_trd_isIntegerRat_of_mem hR hm
  obtain ⟨k, hk⟩ := cd123m5_hom_nrd_isIntegerRat_of_mem hR hm
  have hτ : (1 / (f : ℚ)) • ((m : ℚ) • (1 : ℍ[ℚ, a, b]) + α)
      = ((m : ℚ) / f) • (1 : ℍ[ℚ, a, b]) + (1 / (f : ℚ)) • α := by
    rw [smul_add, smul_smul, one_div_mul_eq_div]
  rw [hτ, kw_ccr25a5_trd_plane, ← hT] at hu
  rw [hτ, kw_ccr25a5_nrd_plane, ← hT, ← hN] at hk
  refine ⟨u, k, ?_, ?_⟩
  · have : ((f : ℤ) : ℚ) * u = ((2 * m + T : ℤ) : ℚ) := by
      rw [hu]; push_cast; field_simp
    exact_mod_cast this
  · have : (((f : ℤ) ^ 2 : ℤ) : ℚ) * k = ((m ^ 2 + m * T + N : ℤ) : ℚ) := by
      rw [hk]; push_cast; field_simp
    exact_mod_cast this

theorem kw_ccr25a5_plane_sub_of_hasConductorPred
    {R₁ R₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder R₁) (h₂ : IsOrder R₂) {α : ℍ[ℚ, a, b]} (hα₁ : α ∈ R₁)
    (hα₂ : α ∈ R₂) (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) {f : ℕ} (hf : 0 < f)
    (hc₁ : kw_surge_e17l3co_hasConductorPred R₁ α f)
    (hc₂ : kw_surge_e17l3co_hasConductorPred R₂ α f) :
    ∀ x : ℍ[ℚ, a, b], (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) → x ∈ R₁ → x ∈ R₂ := by
  have hf0 : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  obtain ⟨m₁, hτ₁⟩ := kw_ccr25a5_exists_generator h₁ hα₁ hnc hf hc₁
  obtain ⟨m₂, hτ₂⟩ := kw_ccr25a5_exists_generator h₂ hα₂ hnc hf hc₂
  obtain ⟨T, hT⟩ := cd123m5_hom_trd_isIntegerRat_of_mem h₁ hα₁
  obtain ⟨N, hN⟩ := cd123m5_hom_nrd_isIntegerRat_of_mem h₁ hα₁
  obtain ⟨u₁, k₁, hu₁, hk₁⟩ := kw_ccr25a5_generator_int_eqs h₁ hT hN hf hτ₁
  obtain ⟨u₂, k₂, hu₂, hk₂⟩ := kw_ccr25a5_generator_int_eqs h₂ hT hN hf hτ₂
  obtain ⟨w, hw⟩ := kw_ccr25a5_parity_core (by exact_mod_cast hf.ne') hu₁ hu₂ hk₁ hk₂

  have hτ₁₂ : (1 / (f : ℚ)) • ((m₁ : ℚ) • (1 : ℍ[ℚ, a, b]) + α)
      = (1 / (f : ℚ)) • ((m₂ : ℚ) • (1 : ℍ[ℚ, a, b]) + α) + (w : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    have hm : (m₁ : ℚ) = m₂ + f * w := by
      have : ((m₁ : ℤ) : ℚ) = ((m₂ + f * w : ℤ) : ℚ) := by rw [← sub_eq_iff_eq_add'.mp hw]
      push_cast at this; exact this
    rw [hm, add_smul, add_assoc, add_comm (((f : ℚ) * w) • (1 : ℍ[ℚ, a, b])) α, ← add_assoc, smul_add,
      smul_smul, one_div, inv_mul_cancel_left₀ hf0]
  have hτ₁R₂ : (1 / (f : ℚ)) • ((m₁ : ℚ) • (1 : ℍ[ℚ, a, b]) + α) ∈ R₂ := by
    rw [hτ₁₂, Int.cast_smul_eq_zsmul]
    exact R₂.add_mem hτ₂ (R₂.smul_mem w h₂.one_mem)

  rintro x ⟨c, e, rfl⟩ hx
  obtain ⟨p, q, hp, hq⟩ := kw_ccr25a5_coeffs_int_of_condStep hnc hc₁.1 hx
  have hdec : c • (1 : ℍ[ℚ, a, b]) + e • α
      = (c - q * m₁ / f) • (1 : ℍ[ℚ, a, b])
        + (q : ℚ) • ((1 / (f : ℚ)) • ((m₁ : ℚ) • (1 : ℍ[ℚ, a, b]) + α)) := by
    have he : e = q / f := by rw [hq, mul_div_cancel_left₀ _ hf0]
    rw [he, smul_smul, smul_add, smul_smul, sub_smul, one_div]
    field_simp
    abel
  have hy : (c - q * m₁ / f) • (1 : ℍ[ℚ, a, b]) ∈ R₁ := by
    have : (c - q * m₁ / f) • (1 : ℍ[ℚ, a, b])
        = (c • (1 : ℍ[ℚ, a, b]) + e • α) - (q : ℚ) • ((1 / (f : ℚ)) • ((m₁ : ℚ) • (1 : ℍ[ℚ, a, b]) + α)) := by
      rw [hdec, add_sub_cancel_right]
    rw [this, Int.cast_smul_eq_zsmul]
    exact R₁.sub_mem hx (R₁.smul_mem q hτ₁)
  obtain ⟨k, hk⟩ := kw_ccr25a5_int_of_ratsmul_one_mem h₁ hy
  rw [hdec, ← hk, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact R₂.add_mem (R₂.smul_mem k h₂.one_mem) (R₂.smul_mem q hτ₁R₂)

theorem kw_ccr25a5_plane_iff_of_hasConductorPred
    {R₁ R₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder R₁) (h₂ : IsOrder R₂) {α : ℍ[ℚ, a, b]} (hα₁ : α ∈ R₁)
    (hα₂ : α ∈ R₂) (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) {f : ℕ} (hf : 0 < f)
    (hc₁ : kw_surge_e17l3co_hasConductorPred R₁ α f)
    (hc₂ : kw_surge_e17l3co_hasConductorPred R₂ α f) :
    ∀ x : ℍ[ℚ, a, b], (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) → (x ∈ R₁ ↔ x ∈ R₂) :=
  fun x hx =>
    ⟨kw_ccr25a5_plane_sub_of_hasConductorPred h₁ h₂ hα₁ hα₂ hnc hf hc₁ hc₂ x hx,
      kw_ccr25a5_plane_sub_of_hasConductorPred h₂ h₁ hα₂ hα₁ hnc hf hc₂ hc₁ x hx⟩

end Uniqueness

end Q15e3
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"

def q15_conjLinear {a b : ℚ} (g : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b] →ₗ[ℚ] ℍ[ℚ, a, b] :=
  (LinearMap.mulLeft ℚ (g : ℍ[ℚ, a, b])).comp (LinearMap.mulRight ℚ ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]))

def q15_plane {a b : ℚ} (α : ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b] := {x | ∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α}

theorem q15_isUnit_of_ne_zero {a b : ℚ} (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : IsUnit x :=
  Q15e3.isUnit_of_ne_zero ha hb hx

theorem q15_skolemNoether {a b : ℚ} (ha : a < 0) (hb : b < 0) {t n : ℤ} {α α' : ℍ[ℚ, a, b]}
    (hα : QuaternionAlgebra.IsQuadraticDatum t n α) (hα' : QuaternionAlgebra.IsQuadraticDatum t n α')
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) :
    ∃ g : ℍ[ℚ, a, b]ˣ, ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) * α * g = α' :=
  Q15e3.kw_ccr25a5_skolemNoether ha hb hα hα' hnc

theorem q15_plane_inter_eq_of_hasEmbeddingConductor {a b : ℚ} (ha : a < 0) (hb : b < 0)
    (Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (h₁ : QuaternionAlgebra.IsOrder Λ₁) (h₂ : QuaternionAlgebra.IsOrder Λ₂)
    {t n : ℤ} {α : ℍ[ℚ, a, b]} (hq : QuaternionAlgebra.IsQuadraticDatum t n α)
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (hα₁ : α ∈ Λ₁) (hα₂ : α ∈ Λ₂)
    {f : ℕ} (hf : 0 < f) (hc₁ : QuaternionAlgebra.HasEmbeddingConductor Λ₁ α f)
    (hc₂ : QuaternionAlgebra.HasEmbeddingConductor Λ₂ α f) :
    ∀ x ∈ q15_plane α, x ∈ Λ₁ ↔ x ∈ Λ₂ :=
  fun x hx => Q15e3.kw_ccr25a5_plane_iff_of_hasConductorPred h₁ h₂ hα₁ hα₂ hnc hf hc₁ hc₂ x hx

namespace Q15e3
section Transport
variable {a b : ℚ}

theorem conj_apply (g : ℍ[ℚ, a, b]ˣ) (x : ℍ[ℚ, a, b]) :
    q15_conjLinear g x = (g : ℍ[ℚ, a, b]) * (x * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) := rfl

theorem conj_eq (g : ℍ[ℚ, a, b]ˣ) (x : ℍ[ℚ, a, b]) :
    q15_conjLinear g x = (g : ℍ[ℚ, a, b]) * x * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) := by
  rw [conj_apply, mul_assoc]

theorem conj_one (g : ℍ[ℚ, a, b]ˣ) : q15_conjLinear g 1 = 1 := by
  rw [conj_apply, one_mul, Units.mul_inv]

theorem conj_plane (g : ℍ[ℚ, a, b]ˣ) (α : ℍ[ℚ, a, b]) (c e : ℚ) :
    q15_conjLinear g (c • (1 : ℍ[ℚ, a, b]) + e • α) = c • (1 : ℍ[ℚ, a, b]) + e • q15_conjLinear g α := by
  rw [map_add, map_smul, map_smul, conj_one]

theorem conj_injective (g : ℍ[ℚ, a, b]ˣ) : Function.Injective (q15_conjLinear g) := by
  intro x y h
  rw [conj_apply, conj_apply, Units.mul_right_inj, Units.mul_left_inj] at h
  exact h

theorem mem_map_conj_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : ℍ[ℚ, a, b]ˣ) (x : ℍ[ℚ, a, b]) :
    x ∈ Λ.map ((q15_conjLinear g).restrictScalars ℤ) ↔ ∃ y ∈ Λ, q15_conjLinear g y = x := by
  rw [Submodule.mem_map]
  rfl

theorem condStep_map_conj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {α : ℍ[ℚ, a, b]} (g : ℍ[ℚ, a, b]ˣ) {k : ℕ}
    (h : kw_surge_e17l3co_condStepPred Λ α k) :
    kw_surge_e17l3co_condStepPred (Λ.map ((q15_conjLinear g).restrictScalars ℤ))
      ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) k := by
  intro x hx hplane
  obtain ⟨c, e, hce⟩ := hplane
  obtain ⟨y, hy, rfl⟩ := (mem_map_conj_iff Λ g x).mp hx
  have hyce : y = c • (1 : ℍ[ℚ, a, b]) + e • α := by
    apply conj_injective g
    rw [hce, conj_plane, conj_eq]
  obtain ⟨p, q, hpq⟩ := h y hy ⟨c, e, hyce⟩
  refine ⟨p, q, ?_⟩
  rw [← map_smul, hpq, conj_plane, conj_eq]

theorem condStep_of_map_conj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {α : ℍ[ℚ, a, b]} (g : ℍ[ℚ, a, b]ˣ) {k : ℕ}
    (h : kw_surge_e17l3co_condStepPred (Λ.map ((q15_conjLinear g).restrictScalars ℤ))
      ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) k) :
    kw_surge_e17l3co_condStepPred Λ α k := by
  intro y hy hplane
  obtain ⟨c, e, hce⟩ := hplane
  have hx : q15_conjLinear g y ∈ Λ.map ((q15_conjLinear g).restrictScalars ℤ) :=
    (mem_map_conj_iff Λ g _).mpr ⟨y, hy, rfl⟩
  have hxplane : ∃ c e : ℚ, q15_conjLinear g y = c • (1 : ℍ[ℚ, a, b]) + e • ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) :=
    ⟨c, e, by rw [hce, conj_plane, conj_eq]⟩
  obtain ⟨p, q, hpq⟩ := h _ hx hxplane
  refine ⟨p, q, conj_injective g ?_⟩
  rw [map_smul, hpq, conj_plane, conj_eq]

end Transport
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"
end Q15e3
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"

theorem q15_mem_map_conj {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {α : ℍ[ℚ, a, b]} (hα : α ∈ Λ) (g : ℍ[ℚ, a, b]ˣ) :
    (g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) ∈ Λ.map ((q15_conjLinear g).restrictScalars ℤ) :=
  (Q15e3.mem_map_conj_iff Λ g _).mpr ⟨α, hα, (Q15e3.conj_eq g α)⟩

theorem q15_isQuadraticDatum_conj {a b : ℚ} {t n : ℤ} {α : ℍ[ℚ, a, b]}
    (h : QuaternionAlgebra.IsQuadraticDatum t n α) (g : ℍ[ℚ, a, b]ˣ) :
    QuaternionAlgebra.IsQuadraticDatum t n ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) := by
  unfold QuaternionAlgebra.IsQuadraticDatum at h ⊢
  set u : ℍ[ℚ, a, b] := (g : ℍ[ℚ, a, b]) with hu
  set v : ℍ[ℚ, a, b] := ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) with hv
  have hvu : v * u = 1 := by rw [hu, hv]; exact Units.inv_mul g
  have huv : u * v = 1 := by rw [hu, hv]; exact Units.mul_inv g
  have e3 : u * α * v * (u * α * v) = u * (α * α) * v := by
    rw [show u * α * v * (u * α * v) = u * α * (v * u) * α * v from by noncomm_ring, hvu]
    noncomm_ring
  calc u * α * v * (u * α * v) - (t : ℚ) • (u * α * v) + (n : ℚ) • (1 : ℍ[ℚ, a, b])
      = u * (α * α) * v - (t : ℚ) • (u * α * v) + (n : ℚ) • (u * 1 * v) := by rw [e3, mul_one, huv]
    _ = u * (α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b])) * v := by
        rw [mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm (t : ℚ) u α, smul_mul_assoc,
          mul_smul_comm (n : ℚ) u (1 : ℍ[ℚ, a, b]), smul_mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

theorem q15_hasEmbeddingConductor_map_conj {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) (g : ℍ[ℚ, a, b]ˣ)
    (h : QuaternionAlgebra.HasEmbeddingConductor Λ α f) :
    QuaternionAlgebra.HasEmbeddingConductor (Λ.map ((q15_conjLinear g).restrictScalars ℤ)) ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) f :=
  ⟨Q15e3.condStep_map_conj g h.1, fun k hk hkf hstep => h.2 k hk hkf (Q15e3.condStep_of_map_conj g hstep)⟩

theorem q15_hasEmbeddingConductor_of_map_conj {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) (g : ℍ[ℚ, a, b]ˣ)
    (h : QuaternionAlgebra.HasEmbeddingConductor (Λ.map ((q15_conjLinear g).restrictScalars ℤ)) ((g : ℍ[ℚ, a, b]) * α * ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b])) f) :
    QuaternionAlgebra.HasEmbeddingConductor Λ α f :=
  ⟨Q15e3.condStep_of_map_conj g h.1, fun k hk hkf hstep => h.2 k hk hkf (Q15e3.condStep_map_conj g hstep)⟩

namespace Q15e3
section ConjOrder
variable {a b : ℚ}

theorem conj_conj_inv (g : ℍ[ℚ, a, b]ˣ) (x : ℍ[ℚ, a, b]) : q15_conjLinear g (q15_conjLinear g⁻¹ x) = x := by
  rw [conj_apply, conj_apply, inv_inv]
  simp only [← mul_assoc, Units.mul_inv, one_mul]
  rw [mul_assoc, Units.mul_inv, mul_one]

theorem conj_surjective (g : ℍ[ℚ, a, b]ˣ) : Function.Surjective (q15_conjLinear g) :=
  fun x => ⟨q15_conjLinear g⁻¹ x, conj_conj_inv g x⟩

theorem conj_mul (g : ℍ[ℚ, a, b]ˣ) (x y : ℍ[ℚ, a, b]) :
    q15_conjLinear g (x * y) = q15_conjLinear g x * q15_conjLinear g y := by
  simp only [conj_apply, mul_assoc, Units.inv_mul_cancel_left]

end ConjOrder
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"
end Q15e3
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"

theorem q15_mem_map_conj_iff {a b : ℚ} (O : Submodule ℤ ℍ[ℚ, a, b]) (g : ℍ[ℚ, a, b]ˣ) (x : ℍ[ℚ, a, b]) :
    x ∈ O.map ((q15_conjLinear g).restrictScalars ℤ) ↔ ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) * x * g ∈ O := by
  rw [Q15e3.mem_map_conj_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Q15e3.conj_apply]
    simpa only [mul_assoc, Units.inv_mul, Units.mul_inv, mul_one, one_mul, Units.inv_mul_cancel_left,
      Units.mul_inv_cancel_left] using hy
  · intro h
    refine ⟨((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) * x * g, h, ?_⟩
    have : ((g⁻¹ : ℍ[ℚ, a, b]ˣ) : ℍ[ℚ, a, b]) * x * g = q15_conjLinear g⁻¹ x := by
      rw [Q15e3.conj_eq, inv_inv]
    rw [this, Q15e3.conj_conj_inv]

theorem q15_isOrder_map_conj {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O) (g : ℍ[ℚ, a, b]ˣ) :
    QuaternionAlgebra.IsOrder (O.map ((q15_conjLinear g).restrictScalars ℤ)) where
  one_mem := (Q15e3.mem_map_conj_iff O g 1).mpr ⟨1, hO.one_mem, Q15e3.conj_one g⟩
  mul_mem := by
    intro x y hx hy
    obtain ⟨x', hx', rfl⟩ := (Q15e3.mem_map_conj_iff O g x).mp hx
    obtain ⟨y', hy', rfl⟩ := (Q15e3.mem_map_conj_iff O g y).mp hy
    exact (Q15e3.mem_map_conj_iff O g _).mpr ⟨x' * y', hO.mul_mem hx' hy', Q15e3.conj_mul g x' y'⟩
  spanTop := by
    have hset : ((O.map ((q15_conjLinear g).restrictScalars ℤ) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])
        = q15_conjLinear g '' (O : Set ℍ[ℚ, a, b]) := Submodule.map_coe _ _
    rw [hset, Submodule.span_image, hO.spanTop, Submodule.map_top, LinearMap.range_eq_top]
    exact Q15e3.conj_surjective g
  fg := hO.fg.map _

theorem q15_mem_plane_of_commute_of_ne {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) {α x : ℍ[ℚ, a, b]}
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (h : x * α = α * x) : x ∈ q15_plane α := by
  obtain ⟨r, i, j, k⟩ := α
  obtain ⟨w, p, q, s⟩ := x
  have hre := congrArg QuaternionAlgebra.re h
  have hI := congrArg QuaternionAlgebra.imI h
  have hJ := congrArg QuaternionAlgebra.imJ h
  have hK := congrArg QuaternionAlgebra.imK h
  simp only [QuaternionAlgebra.mk_mul_mk] at hI hJ hK

  have eK : p * j = q * i := by
    linear_combination (1/2 : ℚ) * hK
  have eJ : p * k = s * i := by
    have h2 : a * (p * k - s * i) = 0 := by
      linear_combination (1/2 : ℚ) * hJ
    have := (mul_eq_zero.mp h2).resolve_left ha
    linear_combination this
  have eI : s * j = q * k := by
    have h2 : b * (s * j - q * k) = 0 := by
      linear_combination (1/2 : ℚ) * hI
    have := (mul_eq_zero.mp h2).resolve_left hb
    linear_combination this
  simp only [not_and_or] at hnc
  show ∃ c e : ℚ, (⟨w, p, q, s⟩ : ℍ[ℚ, a, b]) = c • (1 : ℍ[ℚ, a, b]) + e • ⟨r, i, j, k⟩
  rcases hnc with hi | hj | hk
  · refine ⟨w - p / i * r, p / i, ?_⟩
    ext <;> simp
    · field_simp
    · rw [div_mul_eq_mul_div, eq_div_iff hi]; linear_combination -eK
    · rw [div_mul_eq_mul_div, eq_div_iff hi]; linear_combination -eJ
  · refine ⟨w - q / j * r, q / j, ?_⟩
    ext <;> simp
    · rw [div_mul_eq_mul_div, eq_div_iff hj]; linear_combination eK
    · field_simp
    · rw [div_mul_eq_mul_div, eq_div_iff hj]; linear_combination eI
  · refine ⟨w - s / k * r, s / k, ?_⟩
    ext <;> simp
    · rw [div_mul_eq_mul_div, eq_div_iff hk]; linear_combination eJ
    · rw [div_mul_eq_mul_div, eq_div_iff hk]; linear_combination -eI
    · field_simp

theorem q15_mem_plane_of_commute {a b : ℚ} (ha : a < 0) (hb : b < 0) {α x : ℍ[ℚ, a, b]}
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (h : x * α = α * x) : x ∈ q15_plane α :=
  q15_mem_plane_of_commute_of_ne ha.ne hb.ne hnc h

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.Q15e3"

theorem solution {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (α : ℍ[ℚ, a, b])
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (x : ℍ[ℚ, a, b]) :
    x * α = α * x ↔ ∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α := by
  constructor
  · exact fun h => q15_mem_plane_of_commute_of_ne ha hb hnc h
  · rintro ⟨c, e, rfl⟩
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul
end P2MW
export P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul (solution)
