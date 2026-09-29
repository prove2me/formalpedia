-- Prove2me | solution 1 for WeierstrassCurve.exists_prePsi_eq_expand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f616b87f-5a9f-5ecd-a171-0bb8df91f442

import Mathlib
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial

noncomputable section

open MvPolynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ b₆ Δ map_Ψ₂Sq b₄ Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq"
namespace Universal
p2m_open "WeierstrassCurve"

abbrev R₀ : Type := MvPolynomial (Fin 5) ℤ

def 𝓦 : WeierstrassCurve R₀ := ⟨X 0, X 1, X 2, X 3, X 4⟩

def univHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) : R₀ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

@[scoped simp] theorem univHom_X0 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 0) = W.a₁ := by simp [univHom]
@[scoped simp] theorem univHom_X1 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 1) = W.a₂ := by simp [univHom]
@[scoped simp] theorem univHom_X2 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 2) = W.a₃ := by simp [univHom]
@[scoped simp] theorem univHom_X3 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 3) = W.a₄ := by simp [univHom]
@[scoped simp] theorem univHom_X4 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 4) = W.a₆ := by simp [univHom]

theorem map_univHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) : 𝓦.map (univHom W) = W := by
  ext
  · show univHom W (X 0) = W.a₁; simp
  · show univHom W (X 1) = W.a₂; simp
  · show univHom W (X 2) = W.a₃; simp
  · show univHom W (X 3) = W.a₄; simp
  · show univHom W (X 4) = W.a₆; simp

abbrev Rp (p : ℕ) : Type := MvPolynomial (Fin 5) (ZMod p)

abbrev Fp (p : ℕ) [Fact p.Prime] : Type := FractionRing (Rp p)

def 𝓦p (p : ℕ) : WeierstrassCurve (Rp p) := ⟨X 0, X 1, X 2, X 3, X 4⟩

theorem 𝓦p_eq_map (p : ℕ) : 𝓦p p = 𝓦.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · show (X 0 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 0); rw [MvPolynomial.map_X]
  · show (X 1 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 1); rw [MvPolynomial.map_X]
  · show (X 2 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 2); rw [MvPolynomial.map_X]
  · show (X 3 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 3); rw [MvPolynomial.map_X]
  · show (X 4 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 4); rw [MvPolynomial.map_X]

def univHomP {R : Type*} [CommRing R] (p : ℕ) [CharP R p] (W : WeierstrassCurve R) : Rp p →+* R :=
  MvPolynomial.eval₂Hom (ZMod.castHom (dvd_refl p) R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_univHomP {R : Type*} [CommRing R] (p : ℕ) [CharP R p] (W : WeierstrassCurve R) :
    (𝓦p p).map (univHomP p W) = W := by
  ext
  · show univHomP p W (X 0) = W.a₁; simp [univHomP]
  · show univHomP p W (X 1) = W.a₂; simp [univHomP]
  · show univHomP p W (X 2) = W.a₃; simp [univHomP]
  · show univHomP p W (X 3) = W.a₄; simp [univHomP]
  · show univHomP p W (X 4) = W.a₆; simp [univHomP]

def ev1728 (p : ℕ) : Rp p →+* ZMod p := MvPolynomial.eval ![0, 0, 0, 1, 0]

theorem map_ev1728 (p : ℕ) : (𝓦p p).map (ev1728 p) = WeierstrassCurve.ofJ1728 (ZMod p) := by
  ext
  · show ev1728 p (X 0) = 0; simp [ev1728]
  · show ev1728 p (X 1) = 0; simp [ev1728]
  · show ev1728 p (X 2) = 0; simp [ev1728]
  · show ev1728 p (X 3) = 1; simp [ev1728]
  · show ev1728 p (X 4) = 0; simp [ev1728]

theorem two_ne_zero_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem Δ_𝓦p_ne_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (𝓦p p).Δ ≠ 0 := by
  intro h
  have := congrArg (ev1728 p) h
  rw [← WeierstrassCurve.map_Δ, map_ev1728, WeierstrassCurve.ofJ1728_Δ, map_zero, neg_eq_zero,
    show (64 : ZMod p) = 2 ^ 6 by norm_num] at this
  exact pow_ne_zero 6 (two_ne_zero_zmod p hp2) this

scoped instance charP_Fp (p : ℕ) [Fact p.Prime] : CharP (Fp p) p :=
  charP_of_injective_algebraMap (IsFractionRing.injective (Rp p) (Fp p)) p

theorem isElliptic_𝓦p_Fp (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((𝓦p p).map (algebraMap (Rp p) (Fp p))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
  exact fun h => Δ_𝓦p_ne_zero p hp2 ((IsFractionRing.injective (Rp p) (Fp p)) (by rw [h, map_zero]))

theorem two_ne_zero_Fp (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : Fp p) ≠ 0 := by
  have : ((2 : ℕ) : Fp p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (Fp p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem four_ne_zero_Rp (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (4 : Rp p) ≠ 0 := by
  have h2 : ((2 : ℕ) : Rp p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (Rp p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have : (4 : Rp p) = ((2 : ℕ) : Rp p) ^ 2 := by norm_num
  rw [this]; exact pow_ne_zero 2 h2

end WeierstrassCurve.Universal
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ b₆ Δ map_Ψ₂Sq b₄ Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq"
namespace S1Tail
p2m_open "WeierstrassCurve"

theorem aeval_derivative_mul_sub_mul_eq_zero {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (D : Derivation K L L) {x q : L} (Φ S : K[X]) (hq : q * aeval x S = aeval x Φ) (hDq : D q = 0) :
    aeval x (derivative Φ * S - Φ * derivative S) * D x = 0 := by
  have e := congrArg D hq
  rw [Derivation.leibniz, hDq, smul_zero, add_zero, Derivation.map_aeval, Derivation.map_aeval,
    smul_eq_mul, smul_eq_mul] at e

  simp only [map_sub, map_mul]
  linear_combination -(aeval x S) * e + (aeval x (derivative S) * D x) * hq

theorem aeval_derivative_mul_sub_eq_zero {K L : Type*} [Field K] [CommRing L] [IsDomain L] [Algebra K L]
    (D : Derivation K L L) {x q : L} (hx : D x ≠ 0) (Φ S : K[X]) (hq : q * aeval x S = aeval x Φ)
    (hDq : D q = 0) : aeval x (derivative Φ * S - Φ * derivative S) = 0 :=
  (mul_eq_zero.mp (aeval_derivative_mul_sub_mul_eq_zero D Φ S hq hDq)).resolve_right hx

theorem derivative_mul_sub_eq_zero_of_injective {K L : Type*} [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] (D : Derivation K L L) {x q : L} (hinj : Function.Injective (aeval x : K[X] → L))
    (hx : D x ≠ 0) (Φ S : K[X]) (hq : q * aeval x S = aeval x Φ) (hDq : D q = 0) :
    derivative Φ * S - Φ * derivative S = 0 :=
  hinj (by rw [aeval_derivative_mul_sub_eq_zero D hx Φ S hq hDq, map_zero])

theorem derivative_eq_zero_of_isCoprime_of_wronskian {K : Type*} [CommRing K] [IsDomain K] {Φ S : K[X]}
    (hS : S ≠ 0) (hcop : IsCoprime Φ S) (h : derivative Φ * S - Φ * derivative S = 0) :
    derivative S = 0 := by
  have hdvd : S ∣ Φ * derivative S := ⟨derivative Φ, by linear_combination -h⟩
  have hd : S ∣ derivative S := hcop.symm.dvd_of_dvd_mul_left hdvd
  by_contra hne
  exact absurd (degree_derivative_lt hS) (not_lt.mpr (degree_le_of_dvd hd hne))

theorem derivative_eq_zero_of_derivative_sq {K : Type*} [CommRing K] [IsDomain K] (h2 : (2 : K) ≠ 0)
    {Ψ : K[X]} (hΨ : Ψ ≠ 0) (h : derivative (Ψ ^ 2) = 0) : derivative Ψ = 0 := by
  have hsq : derivative (Ψ ^ 2) = C 2 * Ψ * derivative Ψ := by
    rw [pow_two, derivative_mul, map_ofNat C 2]; ring
  rw [hsq, mul_eq_zero, mul_eq_zero, C_eq_zero] at h
  rcases h with (h | h) | h
  · exact absurd h h2
  · exact absurd h hΨ
  · exact h

theorem derivative_eq_zero_of_isCoprime {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {Φ Ψ : K[X]}
    (hΨ : Ψ ≠ 0) (hcop : IsCoprime Φ Ψ) (h : derivative Φ * Ψ ^ 2 - Φ * derivative (Ψ ^ 2) = 0) :
    derivative Ψ = 0 := by
  have hsq : derivative (Ψ ^ 2) = 2 * Ψ * derivative Ψ := by
    rw [pow_two, derivative_mul]; ring
  rw [hsq] at h

  have h1 : Ψ * (derivative Φ * Ψ - 2 * Φ * derivative Ψ) = 0 := by linear_combination h
  have h1' : derivative Φ * Ψ - 2 * Φ * derivative Ψ = 0 := (mul_eq_zero.mp h1).resolve_left hΨ

  have hdvd : Ψ ∣ Φ * (2 * derivative Ψ) := ⟨derivative Φ, by linear_combination -h1'⟩

  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨c, hc⟩ := hdvd
  have h2d : Ψ ∣ 2 * derivative Ψ :=
    ⟨a * c + b * (2 * derivative Ψ), by linear_combination -(2 * derivative Ψ) * hab + a * hc⟩

  by_contra hne
  have hC2 : (2 : K[X]) = C 2 := (map_ofNat C 2).symm
  have h2ne : (2 : K[X]) * derivative Ψ ≠ 0 := by
    rw [hC2]; exact mul_ne_zero (C_ne_zero.mpr h2) hne
  have hle := degree_le_of_dvd h2d h2ne
  rw [hC2, degree_C_mul h2] at hle
  exact absurd (degree_derivative_lt hΨ) (not_lt.mpr hle)

theorem exists_eq_expand_of_derivative_eq_zero {R : Type*} [CommRing R] [NoZeroDivisors R] (p : ℕ)
    [hp : Fact p.Prime] [CharP R p] {f : R[X]} (hf : derivative f = 0) : ∃ g : R[X], f = expand R p g :=
  ⟨contract p f, (expand_contract p hf hp.out.ne_zero).symm⟩

theorem map_contract {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {p : ℕ} (hp : p ≠ 0)
    (f : R[X]) : (contract p f).map φ = contract p (f.map φ) := by
  ext n
  simp only [coeff_map, coeff_contract hp]

theorem exists_eq_expand_of_map_eq_expand {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {p : ℕ} (hp : p ≠ 0) {f : R[X]} {g : S[X]}
    (h : f.map φ = expand S p g) : ∃ g₀ : R[X], f = expand R p g₀ := by
  refine ⟨contract p f, Polynomial.map_injective φ hφ ?_⟩
  rw [map_expand, map_contract φ hp, h, contract_expand p hp]

theorem preΨ'_map_eq_expand {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (φ : R →+* S) (p : ℕ) {g : R[X]} (h : W.preΨ' p = expand R p g) :
    (W.map φ).preΨ' p = expand S p (g.map φ) := by
  rw [WeierstrassCurve.map_preΨ', h, map_expand]

theorem exists_preΨ'_eq_expand_of_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (φ : R →+* S) (p : ℕ) (h : ∃ g : R[X], W.preΨ' p = expand R p g) :
    ∃ g' : S[X], (W.map φ).preΨ' p = expand S p g' := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.map φ, preΨ'_map_eq_expand W φ p hg⟩

end WeierstrassCurve.S1Tail
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ b₆ Δ map_Ψ₂Sq b₄ Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq"
p2m_open "WeierstrassCurve"

variable {R : Type*} [CommRing R]

def wrLHS (W : WeierstrassCurve R) (n : ℤ) : R[X] :=
  W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2

def wrRHS (W : WeierstrassCurve R) (n : ℤ) : R[X] :=
  C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
    + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3))

def UIdentity (W : WeierstrassCurve R) (n : ℤ) : Prop :=
  W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
    C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
      + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3))

theorem uIdentity_iff (W : WeierstrassCurve R) (n : ℤ) : UIdentity W n ↔ wrLHS W n = wrRHS W n := Iff.rfl

variable {S : Type*} [CommRing S]

theorem wrLHS_map (W : WeierstrassCurve R) (f : R →+* S) (n : ℤ) :
    (wrLHS W n).map f = wrLHS (W.map f) n := by
  simp only [wrLHS, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, derivative_map,
    map_Ψ₂Sq, map_Φ, map_ΨSq]

theorem wrRHS_map (W : WeierstrassCurve R) (f : R →+* S) (n : ℤ) :
    (wrRHS W n).map f = wrRHS (W.map f) n := by
  simp only [wrRHS, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, map_Φ,
    map_ΨSq, map_b₂, map_b₄, map_b₆]
  rw [map_pow f, map_intCast, map_ofNat f 4, map_mul f, map_ofNat f 2]

theorem UIdentity.map {W : WeierstrassCurve R} {n : ℤ} (h : UIdentity W n) (f : R →+* S) :
    UIdentity (W.map f) n := by
  rw [uIdentity_iff] at h ⊢
  rw [← wrLHS_map, ← wrRHS_map, h]

theorem UIdentity.of_map {W : WeierstrassCurve R} {n : ℤ} (f : R →+* S) (hf : Function.Injective f)
    (h : UIdentity (W.map f) n) : UIdentity W n := by
  rw [uIdentity_iff] at h ⊢
  rw [← wrLHS_map, ← wrRHS_map] at h
  exact Polynomial.map_injective f hf h

namespace Universal

open WeierstrassCurve.S1Tail

theorem Ψ₂Sq_𝓦p_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (𝓦p p).Ψ₂Sq ≠ 0 := by
  intro h
  have := congrArg (fun q => Polynomial.coeff q 3) h
  simp [WeierstrassCurve.Ψ₂Sq, coeff_X, coeff_C, coeff_X_pow] at this
  exact four_ne_zero_Rp p hp2 this

theorem wronskian_𝓦p_eq_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hU : UIdentity (𝓦p p) p) :
    derivative ((𝓦p p).Φ p) * (𝓦p p).ΨSq p - (𝓦p p).Φ p * derivative ((𝓦p p).ΨSq p) = 0 := by
  have hp0 : (((p : ℤ) : Rp p)) = 0 := by
    rw [Int.cast_natCast]; exact CharP.cast_eq_zero (Rp p) p
  rw [UIdentity, hp0, zero_pow two_ne_zero, map_zero, zero_mul, mul_eq_zero] at hU
  exact pow_eq_zero_iff two_ne_zero |>.mp (hU.resolve_left (Ψ₂Sq_𝓦p_ne_zero p hp2))

theorem derivative_preΨ'_𝓦p_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hU : UIdentity (𝓦p p) p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p)) :
    derivative ((𝓦p p).preΨ' p) = 0 := by
  by_cases hΨ : (𝓦p p).preΨ' p = 0
  · rw [hΨ, derivative_zero]
  set ι := algebraMap (Rp p) (Fp p) with hι
  have hinj : Function.Injective ι := IsFractionRing.injective (Rp p) (Fp p)
  have hodd : ¬ Even p := fun h => hp2 (hp.out.even_iff.mp h)

  have hW := congrArg (Polynomial.map ι) (wronskian_𝓦p_eq_zero p hp2 hU)
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, ← derivative_map,
    ← map_Φ, ← map_ΨSq, Polynomial.map_zero] at hW

  have hSq : ((𝓦p p).map ι).ΨSq p = ((𝓦p p).map ι).preΨ' p ^ 2 := by
    rw [ΨSq_ofNat, if_neg hodd, mul_one]
  have hΨF : ((𝓦p p).map ι).preΨ' p ≠ 0 := by
    rw [map_preΨ']; exact fun h => hΨ (Polynomial.map_injective ι hinj (by rw [h, Polynomial.map_zero]))
  have hSqne : ((𝓦p p).map ι).ΨSq p ≠ 0 := by rw [hSq]; exact pow_ne_zero 2 hΨF

  have h1 := derivative_eq_zero_of_isCoprime_of_wronskian hSqne hcop hW
  rw [hSq] at h1
  have h2 := derivative_eq_zero_of_derivative_sq (two_ne_zero_Fp p hp2) hΨF h1

  rw [map_preΨ', derivative_map] at h2
  exact Polynomial.map_injective ι hinj (by rw [h2, Polynomial.map_zero])

theorem derivative_Φ_𝓦p_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hU : UIdentity (𝓦p p) p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p))
    (hΨ : (𝓦p p).preΨ' p ≠ 0) : derivative ((𝓦p p).Φ p) = 0 := by
  have hodd : ¬ Even p := fun h => hp2 (hp.out.even_iff.mp h)
  have hW := wronskian_𝓦p_eq_zero p hp2 hU
  have hd := derivative_preΨ'_𝓦p_eq_zero p hp2 hU hcop
  have hSq : (𝓦p p).ΨSq p = (𝓦p p).preΨ' p ^ 2 := by rw [ΨSq_ofNat, if_neg hodd, mul_one]
  rw [hSq, show derivative ((𝓦p p).preΨ' p ^ 2) = 0 by rw [pow_two, derivative_mul, hd]; ring,
    mul_zero, sub_zero, mul_eq_zero] at hW
  exact hW.resolve_right (pow_ne_zero 2 hΨ)

theorem exists_preΨ'_eq_expand_of_UIdentity (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hU : UIdentity (𝓦p p) p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p))
    {R : Type*} [CommRing R] [CharP R p] (W : WeierstrassCurve R) :
    ∃ g : R[X], W.preΨ' p = expand R p g := by
  obtain ⟨g, hg⟩ := exists_eq_expand_of_derivative_eq_zero p (derivative_preΨ'_𝓦p_eq_zero p hp2 hU hcop)
  rw [← map_univHomP p W]
  exact exists_preΨ'_eq_expand_of_map (𝓦p p) (univHomP p W) p ⟨g, hg⟩

theorem exists_preΨ'_eq_expand_of_UIdentity_int (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hU : UIdentity 𝓦 p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p))
    {R : Type*} [CommRing R] [CharP R p] (W : WeierstrassCurve R) :
    ∃ g : R[X], W.preΨ' p = expand R p g := by
  have hU' : UIdentity (𝓦p p) p := by rw [𝓦p_eq_map]; exact hU.map _
  exact exists_preΨ'_eq_expand_of_UIdentity p hp2 hU' hcop W

end Universal
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ b₆ Δ map_Ψ₂Sq b₄ Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq"
p2m_open "WeierstrassCurve"

open Universal

theorem UIdentity_univ (n : ℤ) : UIdentity 𝓦 n := WeierstrassCurve.Psi2Sq_mul_wronskian_sq 𝓦 n

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve WeierstrassCurve.Universal in

theorem solution {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (W : WeierstrassCurve R) : ∃ g : Polynomial R, W.preΨ' p = Polynomial.expand R p g := by
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨1, by rw [WeierstrassCurve.preΨ'_two, map_one]⟩
  · haveI := isElliptic_𝓦p_Fp p hp2
    exact exists_preΨ'_eq_expand_of_UIdentity_int p hp2 (UIdentity_univ p)
      (WeierstrassCurve.isCoprime_Phi_PsiSq _ (p : ℤ)) W

end S_WeierstrassCurve_exists_prePsi_eq_expand
end P2MW
export P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand (solution)
