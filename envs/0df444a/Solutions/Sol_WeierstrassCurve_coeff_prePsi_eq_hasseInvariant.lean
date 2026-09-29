-- Prove2me | solution 1 for WeierstrassCurve.coeff_prePsi_eq_hasseInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e090718f-d5f8-5b07-b588-bfc1ae49d6d4

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_prePsi_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial

noncomputable section

open MvPolynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ natDegree_Ψ₂Sq_le natDegree_Φ preΨ'_ne_zero map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction leadingCoeff_Ψ₂Sq coeff_preΨ' ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ Ψ₂Sq_eq b₆ Δ coeff_Φ natDegree_preΨ'_le natDegree_Ψ₂Sq leadingCoeff_Φ map_Ψ₂Sq j b₄ hasseInvariant Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq prePsi_ne_zero_of_isElliptic"
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
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ natDegree_Ψ₂Sq_le natDegree_Φ preΨ'_ne_zero map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction leadingCoeff_Ψ₂Sq coeff_preΨ' ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ Ψ₂Sq_eq b₆ Δ coeff_Φ natDegree_preΨ'_le natDegree_Ψ₂Sq leadingCoeff_Φ map_Ψ₂Sq j b₄ hasseInvariant Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq prePsi_ne_zero_of_isElliptic"
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
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ natDegree_Ψ₂Sq_le natDegree_Φ preΨ'_ne_zero map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction leadingCoeff_Ψ₂Sq coeff_preΨ' ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ Ψ₂Sq_eq b₆ Δ coeff_Φ natDegree_preΨ'_le natDegree_Ψ₂Sq leadingCoeff_Φ map_Ψ₂Sq j b₄ hasseInvariant Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq prePsi_ne_zero_of_isElliptic"
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
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ natDegree_Ψ₂Sq_le natDegree_Φ preΨ'_ne_zero map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction leadingCoeff_Ψ₂Sq coeff_preΨ' ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ Ψ₂Sq_eq b₆ Δ coeff_Φ natDegree_preΨ'_le natDegree_Ψ₂Sq leadingCoeff_Φ map_Ψ₂Sq j b₄ hasseInvariant Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq prePsi_ne_zero_of_isElliptic"
namespace Universal
p2m_open "WeierstrassCurve"

open WeierstrassCurve.S1Tail

def red (p : ℕ) : R₀ →+* Rp p := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem 𝓦p_eq_map_red (p : ℕ) : 𝓦p p = 𝓦.map (red p) := 𝓦p_eq_map p

theorem exists_eq_p_mul_of_map_red_eq_zero (p : ℕ) {f : R₀[X]} (hf : f.map (red p) = 0) :
    ∃ g : R₀[X], f = (p : R₀[X]) * g := by
  have hdvd : C (MvPolynomial.C (p : ℤ) : R₀) ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [MvPolynomial.C_dvd_iff_zmod]
    have := congrArg (fun q => q.coeff i) hf
    simpa [coeff_map, red] using this
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨g, ?_⟩
  rw [hg, map_natCast MvPolynomial.C p, map_natCast C p]

def piProj (p : ℕ) {R : Type*} [CommRing R] (f : R[X]) : R[X] := contract p (X * f)

theorem coeff_piProj {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R] (f : R[X]) (k : ℕ) :
    (piProj p f).coeff k = (X * f).coeff (k * p) := by
  rw [piProj, coeff_contract hp]

theorem piProj_add {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R] (f g : R[X]) :
    piProj p (f + g) = piProj p f + piProj p g := by
  ext k; simp only [coeff_piProj hp, mul_add, coeff_add]

theorem piProj_sub {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R] (f g : R[X]) :
    piProj p (f - g) = piProj p f - piProj p g := by
  ext k; simp only [coeff_piProj hp, mul_sub, coeff_sub]

theorem piProj_expand_mul {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R] (u f : R[X]) :
    piProj p (expand R p u * f) = u * piProj p f := by
  rw [piProj, piProj, show X * (expand R p u * f) = (X * f) * expand R p u by ring,
    contract_mul_expand hp, mul_comm]

theorem piProj_X_pow_mul_expand {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R] (Q : R[X]) :
    piProj p (X ^ (p - 1) * expand R p Q) = X * Q := by
  rw [piProj, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp),
    show (X : R[X]) ^ p * expand R p Q = expand R p (X * Q) by rw [map_mul, expand_X],
    contract_expand p hp]

theorem piProj_derivative {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] (f : R[X]) :
    piProj p (derivative f) = 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  ext k
  rw [coeff_piProj hp, coeff_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [zero_mul, coeff_X_mul_zero]
  · obtain ⟨j, hj⟩ : ∃ j, k * p = j + 1 := ⟨k * p - 1, by
      have : 1 ≤ k * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk.ne' hp); omega⟩
    rw [hj, coeff_X_mul, coeff_derivative]
    have : ((j : R) + 1) = ((k * p : ℕ) : R) := by rw [hj]; push_cast; ring
    rw [this, Nat.cast_mul, CharP.cast_eq_zero R p, mul_zero, mul_zero]

theorem piProj_derivative_mul_expand {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (g u : R[X]) : piProj p (derivative g * expand R p u) = 0 := by
  have : derivative g * expand R p u = derivative (g * expand R p u) := by
    rw [derivative_mul, derivative_expand, CharP.cast_eq_zero, zero_mul, mul_zero, mul_zero, add_zero]
  rw [this, piProj_derivative]

theorem pow_char_eq_expand_map_frobenius {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (f : R[X]) : f ^ p = expand R p (f.map (frobenius R p)) := by
  rw [← map_expand, map_frobenius_expand]

section S2

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 16000000 in

theorem coeff_preΨ'_𝓦p_eq_hasseInvariant (hp2 : p ≠ 2) (hU : UIdentity 𝓦 p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p))
    (hΨne : (𝓦p p).preΨ' p ≠ 0) :
    ((𝓦p p).preΨ' p).coeff (p * ((p - 1) / 2)) = (𝓦p p).hasseInvariant p := by

  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := hp.out.odd_of_ne_two hp2
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hppos : 0 < p := hp.out.pos
  have hm1 : (p - 1) / 2 = m := by omega
  have hm2 : p - 1 = 2 * m := by omega
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; subst h; have := hp.out.one_lt; omega
    · exact h
  set k : ℕ := (p ^ 2 - 1) / 2 with hk
  have hpsq : p ^ 2 = 2 * k + 1 := by
    have : p ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by rw [hm]; ring
    omega
  have hk_eq : k = p * m + m := by
    have : p ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by rw [hm]; ring
    have hk2 : k = 2 * m ^ 2 + 2 * m := by omega
    rw [hk2, hm]; ring
  have hnat : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
  have hodd : ¬ Even p := fun h => hp2 (hp.out.even_iff.mp h)

  set Φ : R₀[X] := 𝓦.Φ p with hΦdef
  set Ψ : R₀[X] := 𝓦.preΨ' p with hΨdef
  have hpR : (p : R₀) ≠ 0 := by exact_mod_cast hp0
  have hpRX : (p : R₀[X]) ≠ 0 := by rw [← map_natCast C p]; exact C_ne_zero.mpr hpR
  have hΨ_ne : Ψ ≠ 0 := preΨ'_ne_zero 𝓦 hpR
  have hΦ_coeff : Φ.coeff (p ^ 2) = 1 := by rw [hΦdef, ← hnat]; exact coeff_Φ 𝓦 p
  have hΦ_deg : Φ.natDegree = p ^ 2 := by rw [hΦdef, natDegree_Φ, hnat]
  have hΨ_coeff : Ψ.coeff k = p := by
    have := coeff_preΨ' 𝓦 p
    rw [if_neg hodd, if_neg hodd] at this
    exact this
  have hΨ_deg : Ψ.natDegree ≤ k := by
    have := natDegree_preΨ'_le 𝓦 p
    rw [if_neg hodd] at this
    exact this

  set Wr0 : R₀[X] := derivative Φ * Ψ - C 2 * Φ * derivative Ψ with hWr0
  set G : R₀[X] := C 4 * Φ ^ 3 + C 𝓦.b₂ * Φ ^ 2 * Ψ ^ 2 + C (2 * 𝓦.b₄) * Φ * Ψ ^ 4 + C 𝓦.b₆ * Ψ ^ 6
    with hG
  have hSq : 𝓦.ΨSq p = Ψ ^ 2 := by rw [hΨdef, ΨSq_ofNat, if_neg hodd, mul_one]
  have hA1 : 𝓦.Ψ₂Sq * Wr0 ^ 2 = C ((p : R₀) ^ 2) * G := by
    have hU' := hU
    rw [UIdentity, hSq, Int.cast_natCast] at hU'
    have hder : derivative (Ψ ^ 2) = C 2 * Ψ * derivative Ψ := by
      rw [pow_two, derivative_mul, map_ofNat C 2]; ring
    rw [hder] at hU'

    have e : Ψ ^ 2 * (𝓦.Ψ₂Sq * Wr0 ^ 2 - C ((p : R₀) ^ 2) * G) = 0 := by
      rw [hWr0, hG]; linear_combination hU'
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 hΨ_ne))

  have hΨbar : (𝓦p p).preΨ' p = Ψ.map (red p) := by rw [𝓦p_eq_map_red, map_preΨ']
  have hΦbar : (𝓦p p).Φ p = Φ.map (red p) := by rw [𝓦p_eq_map_red, map_Φ]
  have hU_p : UIdentity (𝓦p p) p := by rw [𝓦p_eq_map_red]; exact hU.map _
  have hdΨbar : derivative ((𝓦p p).preΨ' p) = 0 := derivative_preΨ'_𝓦p_eq_zero p hp2 hU_p hcop
  have hdΦbar : derivative ((𝓦p p).Φ p) = 0 := derivative_Φ_𝓦p_eq_zero p hp2 hU_p hcop hΨne

  have hWr0_red : Wr0.map (red p) = 0 := by
    rw [hWr0, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      ← derivative_map, ← derivative_map, ← hΨbar, ← hΦbar, hdΨbar, hdΦbar]
    simp
  obtain ⟨H, hH⟩ := exists_eq_p_mul_of_map_red_eq_zero p hWr0_red

  have hA4 : 𝓦.Ψ₂Sq * H ^ 2 = G := by
    have h' : 𝓦.Ψ₂Sq * ((p : R₀[X]) * H) ^ 2 = C ((p : R₀) ^ 2) * G := by rw [← hH]; exact hA1
    rw [← map_natCast C p, map_pow] at h'
    have e : (C (p : R₀)) ^ 2 * (𝓦.Ψ₂Sq * H ^ 2 - G) = 0 := by linear_combination h'
    have hC : (C (p : R₀)) ≠ 0 := C_ne_zero.mpr hpR
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 hC))

  have hk1 : 1 ≤ k := by rw [hk_eq]; exact hm_pos.trans (Nat.le_add_left _ _)
  have hdΦdeg : (derivative Φ).natDegree ≤ p ^ 2 - 1 := (natDegree_derivative_le Φ).trans (by rw [hΦ_deg])
  have hdΨdeg : (derivative Ψ).natDegree ≤ k - 1 := (natDegree_derivative_le Ψ).trans (Nat.sub_le_sub_right hΨ_deg 1)
  have h2Φdeg : (C (2 : R₀) * Φ).natDegree ≤ p ^ 2 := (natDegree_C_mul_le _ _).trans hΦ_deg.le
  have hWr0_deg : Wr0.natDegree ≤ 3 * k := by
    rw [hWr0]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le).trans (by omega)
    · exact (natDegree_mul_le).trans (by omega)
  have hWr0_coeff : Wr0.coeff (3 * k) = p := by
    have i1 : 3 * k = (p ^ 2 - 1) + k := by omega
    have i2 : 3 * k = p ^ 2 + (k - 1) := by omega
    have c1 : (derivative Φ * Ψ).coeff (3 * k) = (p : R₀) ^ 2 * p := by
      rw [i1, coeff_mul_add_eq_of_natDegree_le hdΦdeg hΨ_deg, coeff_derivative,
        show p ^ 2 - 1 + 1 = p ^ 2 by omega, hΦ_coeff, hΨ_coeff, one_mul]
      have : ((p ^ 2 - 1 : ℕ) : R₀) + 1 = ((p ^ 2 : ℕ) : R₀) := by rw [← Nat.cast_add_one, show p ^ 2 - 1 + 1 = p ^ 2 by omega]
      rw [this]; push_cast; ring
    have c2 : (C (2 : R₀) * Φ * derivative Ψ).coeff (3 * k) = 2 * (p * k) := by
      rw [i2, coeff_mul_add_eq_of_natDegree_le h2Φdeg hdΨdeg, coeff_C_mul, hΦ_coeff, coeff_derivative,
        show k - 1 + 1 = k by omega, hΨ_coeff]
      have : ((k - 1 : ℕ) : R₀) + 1 = ((k : ℕ) : R₀) := by rw [← Nat.cast_add_one, Nat.sub_add_cancel hk1]
      rw [this]; ring
    have hp2k : ((p : R₀)) ^ 2 = 2 * k + 1 := by exact_mod_cast hpsq
    rw [hWr0, coeff_sub, c1, c2]
    linear_combination (p : R₀) * hp2k
  have hN_coeff : H.coeff (3 * k) = 1 := by
    have e : (p : R₀) * H.coeff (3 * k) = p * 1 := by
      have := hWr0_coeff
      rw [hH, ← map_natCast C p, coeff_C_mul] at this
      rw [mul_one]; exact this
    exact mul_left_cancel₀ hpR e
  have hN_deg : H.natDegree ≤ 3 * k := by
    have : (C (p : R₀) * H).natDegree = H.natDegree := natDegree_C_mul hpR
    rw [← this, map_natCast C p, ← hH]; exact hWr0_deg

  set S : (Rp p)[X] := (𝓦p p).Ψ₂Sq with hS
  set Hb : (Rp p)[X] := H.map (red p) with hHb
  have hS_red : S = 𝓦.Ψ₂Sq.map (red p) := by rw [hS, 𝓦p_eq_map_red, map_Ψ₂Sq]
  have hHb_coeff : Hb.coeff (3 * k) = 1 := by rw [hHb, coeff_map, hN_coeff, map_one]
  have hHb_deg : Hb.natDegree ≤ 3 * k := (natDegree_map_le).trans hN_deg
  have hHb_ne : Hb ≠ 0 := fun h => by rw [h, coeff_zero] at hHb_coeff; exact zero_ne_one hHb_coeff
  set Φt : (Rp p)[X] := contract p ((𝓦p p).Φ p) with hΦt
  set Ψt : (Rp p)[X] := contract p ((𝓦p p).preΨ' p) with hΨt
  have hΦexp : (𝓦p p).Φ p = expand (Rp p) p Φt := (expand_contract p hdΦbar hp0).symm
  have hΨexp : (𝓦p p).preΨ' p = expand (Rp p) p Ψt := (expand_contract p hdΨbar hp0).symm
  set Gt : (Rp p)[X] := C 4 * Φt ^ 3 + C (𝓦p p).b₂ * Φt ^ 2 * Ψt ^ 2 + C (2 * (𝓦p p).b₄) * Φt * Ψt ^ 4
    + C (𝓦p p).b₆ * Ψt ^ 6 with hGt
  have eΦ : Φ.map (red p) = expand (Rp p) p Φt := by rw [← hΦbar, hΦexp]
  have eΨ : Ψ.map (red p) = expand (Rp p) p Ψt := by rw [← hΨbar, hΨexp]
  have eb₂ : red p 𝓦.b₂ = (𝓦p p).b₂ := by rw [𝓦p_eq_map_red, map_b₂]
  have eb₄ : red p 𝓦.b₄ = (𝓦p p).b₄ := by rw [𝓦p_eq_map_red, map_b₄]
  have eb₆ : red p 𝓦.b₆ = (𝓦p p).b₆ := by rw [𝓦p_eq_map_red, map_b₆]
  have hGbar : G.map (red p) = expand (Rp p) p Gt := by
    rw [hG, hGt]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eΦ, eΨ,
      map_ofNat, Polynomial.map_ofNat, map_mul (red p), eb₂, eb₄, eb₆, map_add (expand (Rp p) p),
      map_mul (expand (Rp p) p), map_pow (expand (Rp p) p), expand_C]
  have hB : S * Hb ^ 2 = expand (Rp p) p Gt := by
    rw [hS_red, hHb, ← hGbar, ← Polynomial.map_pow, ← Polynomial.map_mul, hA4]

  have hpRp : ((2 * m + 1 : ℕ) : (Rp p)[X]) = 0 := by rw [← hm]; exact CharP.cast_eq_zero _ p
  have h2Rp : (2 : (Rp p)[X]) ≠ 0 := by
    rw [← map_ofNat C 2]; refine C_ne_zero.mpr ?_
    have := four_ne_zero_Rp p hp2
    intro h; apply this; rw [show (4 : Rp p) = 2 * 2 by norm_num, h, mul_zero]
  have hE : derivative S * Hb + 2 * S * derivative Hb = 0 := by
    have e := congrArg derivative hB
    rw [derivative_expand, CharP.cast_eq_zero, zero_mul, mul_zero, derivative_mul, pow_two, derivative_mul] at e
    have e2 : Hb * (derivative S * Hb + 2 * S * derivative Hb) = 0 := by linear_combination e
    exact (mul_eq_zero.mp e2).resolve_left hHb_ne
  have hder0 : derivative (S ^ (m + 1) * Hb) = 0 := by
    have e : (2 : (Rp p)[X]) * derivative (S ^ (m + 1) * Hb) = 0 := by
      have hpRp' : (2 * (m : (Rp p)[X]) + 1) = 0 := by exact_mod_cast hpRp
      rw [derivative_mul, derivative_pow, map_natCast C (m + 1), Nat.add_sub_cancel]
      push_cast
      linear_combination (S ^ m) * hE + (S ^ m * derivative S * Hb) * hpRp'
    exact (mul_eq_zero.mp e).resolve_left h2Rp
  set V : (Rp p)[X] := contract p (S ^ (m + 1) * Hb) with hV
  have hVexp : S ^ (m + 1) * Hb = expand (Rp p) p V := (expand_contract p hder0 hp0).symm

  set Q : (Rp p)[X] := derivative Φt * Ψt - 2 * Φt * derivative Ψt with hQ
  have hHb_shape : ∃ E : (Rp p)[X], Hb = X ^ (p - 1) * expand (Rp p) p Q + E ∧ piProj p E = 0 := by

    obtain ⟨Rr, hRr⟩ : ∃ Rr, Φ - expand R₀ p (contract p Φ) = (p : R₀[X]) * Rr :=
      exists_eq_p_mul_of_map_red_eq_zero p (by
        rw [Polynomial.map_sub, map_expand, map_contract (red p) hp0, eΦ, contract_expand p hp0, sub_self])
    obtain ⟨Sr, hSr⟩ : ∃ Sr, Ψ - expand R₀ p (contract p Ψ) = (p : R₀[X]) * Sr :=
      exists_eq_p_mul_of_map_red_eq_zero p (by
        rw [Polynomial.map_sub, map_expand, map_contract (red p) hp0, eΨ, contract_expand p hp0, sub_self])
    have hΦ' : derivative Φ = (p : R₀[X]) * (X ^ (p - 1) * expand R₀ p (derivative (contract p Φ)) + derivative Rr) := by
      have e : Φ = expand R₀ p (contract p Φ) + (p : R₀[X]) * Rr := by linear_combination hRr
      conv_lhs => rw [e]
      rw [derivative_add, derivative_expand, derivative_mul, derivative_natCast, zero_mul, zero_add]
      ring
    have hΨ' : derivative Ψ = (p : R₀[X]) * (X ^ (p - 1) * expand R₀ p (derivative (contract p Ψ)) + derivative Sr) := by
      have e : Ψ = expand R₀ p (contract p Ψ) + (p : R₀[X]) * Sr := by linear_combination hSr
      conv_lhs => rw [e]
      rw [derivative_add, derivative_expand, derivative_mul, derivative_natCast, zero_mul, zero_add]
      ring
    set Hx : R₀[X] := (X ^ (p - 1) * expand R₀ p (derivative (contract p Φ)) + derivative Rr) * Ψ
      - C 2 * Φ * (X ^ (p - 1) * expand R₀ p (derivative (contract p Ψ)) + derivative Sr) with hHx
    have hW2 : Wr0 = (p : R₀[X]) * Hx := by rw [hWr0, hΦ', hΨ', hHx]; ring
    have hHHx : H = Hx := mul_left_cancel₀ hpRX (hH.symm.trans hW2)
    have eΦt : contract p (Φ.map (red p)) = Φt := by rw [hΦt, hΦbar]
    have eΨt : contract p (Ψ.map (red p)) = Ψt := by rw [hΨt, hΨbar]
    refine ⟨derivative (Rr.map (red p)) * expand (Rp p) p Ψt
      - derivative (2 * Sr.map (red p)) * expand (Rp p) p Φt, ?_, ?_⟩
    · rw [hHb, hHHx, hHx]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X,
        map_expand, ← derivative_map, map_contract (red p) hp0, Polynomial.map_ofNat, Polynomial.map_C,
        map_ofNat]
      have d2 : ∀ f : (Rp p)[X], derivative (2 * f) = 2 * derivative f := fun f => by
        rw [← map_ofNat C 2, derivative_C_mul]
      rw [eΦt, eΨt, eΦ, eΨ, hQ, d2]
      simp only [map_sub (expand (Rp p) p), map_mul (expand (Rp p) p), map_ofNat]
      ring
    · rw [piProj_sub hp0, piProj_derivative_mul_expand, piProj_derivative_mul_expand, sub_zero]

  set A : Rp p := (𝓦p p).hasseInvariant p with hA
  have h4 : (4 : Rp p) ≠ 0 := four_ne_zero_Rp p hp2
  have hSdeg3 : S.natDegree = 3 := natDegree_Ψ₂Sq _ h4
  have hSm_deg : (S ^ m).natDegree ≤ 3 * m := natDegree_pow_le.trans (by rw [hSdeg3, mul_comm])
  have hA' : A = (S ^ m).coeff (p - 1) := by
    rw [hA, WeierstrassCurve.hasseInvariant, ← Ψ₂Sq_eq, hm1]
  have hπS : piProj p (S ^ m) = C A * X := by
    refine Polynomial.ext fun n => ?_
    rw [coeff_piProj hp0, coeff_C_mul, coeff_X]
    rcases Nat.lt_trichotomy n 1 with hn | rfl | hn
    · have : n = 0 := by omega
      subst this
      rw [zero_mul, coeff_X_mul_zero]; simp
    · have e := coeff_X_mul (S ^ m) (p - 1)
      rw [Nat.sub_add_cancel hppos] at e
      rw [one_mul, e, ← hA']; simp
    · have hn1 : (1 : ℕ) ≠ n := by omega
      have hn1' : n ≠ 1 := by omega
      have h2p : 2 * p ≤ n * p := Nat.mul_le_mul_right p (by omega)
      have e := coeff_X_mul (S ^ m) (n * p - 1)
      rw [show n * p - 1 + 1 = n * p by omega] at e
      rw [e, coeff_eq_zero_of_natDegree_lt (by omega : (S ^ m).natDegree < n * p - 1)]
      simp [hn1, hn1']
  set Cf : (Rp p)[X] := S.map (frobenius (Rp p) p) with hCf
  have hstar : Cf * Q = C A * V := by
    have e1 : expand (Rp p) p Cf * Hb = S ^ m * expand (Rp p) p V := by
      rw [← pow_char_eq_expand_map_frobenius, ← hVexp, ← mul_assoc, ← pow_add,
        show m + (m + 1) = p by omega]
    obtain ⟨E, hHbE, hπE⟩ := hHb_shape
    have e2 := congrArg (piProj p) e1
    rw [piProj_expand_mul hp0, hHbE, piProj_add hp0, piProj_X_pow_mul_expand hp0, hπE, add_zero,
      mul_comm (S ^ m), piProj_expand_mul hp0, hπS] at e2

    have e3 : X * (Cf * Q - C A * V) = 0 := by linear_combination e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left X_ne_zero)

  have hCf_deg : Cf.natDegree ≤ 3 := (natDegree_map_le).trans (natDegree_Ψ₂Sq_le _)
  have hCf_coeff : Cf.coeff 3 = 4 := by
    have hS3 : S.coeff 3 = 4 := by
      have := leadingCoeff_Ψ₂Sq (𝓦p p) h4
      rwa [leadingCoeff, ← hS, hSdeg3] at this
    rw [hCf, coeff_map, hS3, map_ofNat]

  have hΦbar_monic : ((𝓦p p).Φ p).Monic := by rw [hΦbar]; exact (show Φ.Monic from leadingCoeff_Φ 𝓦 p).map _
  have hΦbar_deg : ((𝓦p p).Φ p).natDegree = p ^ 2 := by
    rw [hΦbar, (show Φ.Monic from leadingCoeff_Φ 𝓦 p).natDegree_map, hΦ_deg]
  have hΦt_deg : Φt.natDegree = p := by
    have e : Φt.natDegree * p = p * p := by rw [← natDegree_expand, ← hΦexp, hΦbar_deg, pow_two]
    exact Nat.eq_of_mul_eq_mul_right hppos e
  have hΦt_coeff : Φt.coeff p = 1 := by
    rw [← coeff_expand_mul hppos, ← hΦexp, ← pow_two, ← hΦbar_deg]; exact hΦbar_monic
  have hΨbar_deg : ((𝓦p p).preΨ' p).natDegree ≤ p * m + m := by
    rw [hΨbar, ← hk_eq]; exact natDegree_map_le.trans hΨ_deg
  have hΨt_deg : Ψt.natDegree ≤ m := by
    have e : Ψt.natDegree * p ≤ p * m + m := by rw [← natDegree_expand, ← hΨexp]; exact hΨbar_deg
    have hmp : m < p := by omega
    have : Ψt.natDegree * p < (m + 1) * p := by
      calc Ψt.natDegree * p ≤ p * m + m := e
        _ < p * m + p := by omega
        _ = (m + 1) * p := by ring
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right this)
  have hΨt_coeff : Ψt.coeff m = ((𝓦p p).preΨ' p).coeff (p * m) := by
    rw [← coeff_expand_mul hppos, ← hΨexp, mul_comm]
  have hdΦt_deg : (derivative Φt).natDegree ≤ p - 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_derivative]
    rcases Nat.lt_or_ge p (i + 1) with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hΦt_deg]; exact h), zero_mul]
    · have : i + 1 = p := by omega
      have hc : ((i : Rp p) + 1) = ((p : ℕ) : Rp p) := by rw [← Nat.cast_add_one, this]
      rw [hc, CharP.cast_eq_zero, mul_zero]
  have hdΨt_deg : (derivative Ψt).natDegree ≤ m - 1 := (natDegree_derivative_le Ψt).trans (Nat.sub_le_sub_right hΨt_deg 1)
  have h2Φt_deg : ((2 : (Rp p)[X]) * Φt).natDegree ≤ p := by
    rw [← map_ofNat C 2]; exact (natDegree_C_mul_le _ _).trans hΦt_deg.le
  have hQ1_deg : (derivative Φt * Ψt).natDegree ≤ 3 * m - 1 := natDegree_mul_le.trans (by omega)
  have hQ2_deg : ((2 : (Rp p)[X]) * Φt * derivative Ψt).natDegree ≤ 3 * m := natDegree_mul_le.trans (by omega)
  have hQ_deg : Q.natDegree ≤ 3 * m := by
    rw [hQ]; exact (natDegree_sub_le _ _).trans (max_le (hQ1_deg.trans (by omega)) hQ2_deg)
  have hQ_coeff : Q.coeff (3 * m) = ((𝓦p p).preΨ' p).coeff (p * m) := by
    have c1 : (derivative Φt * Ψt).coeff (3 * m) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have c2 : ((2 : (Rp p)[X]) * Φt * derivative Ψt).coeff (3 * m) = 2 * (((𝓦p p).preΨ' p).coeff (p * m) * m) := by
      rw [show 3 * m = p + (m - 1) by omega, coeff_mul_add_eq_of_natDegree_le h2Φt_deg hdΨt_deg, ← map_ofNat C 2,
        coeff_C_mul, hΦt_coeff, coeff_derivative, show m - 1 + 1 = m by omega, hΨt_coeff]
      have : ((m - 1 : ℕ) : Rp p) + 1 = ((m : ℕ) : Rp p) := by rw [← Nat.cast_add_one, Nat.sub_add_cancel hm_pos]
      rw [this]; ring
    have hpRp'' : (2 * (m : Rp p) + 1) = 0 := by
      have : ((2 * m + 1 : ℕ) : Rp p) = 0 := by rw [← hm]; exact CharP.cast_eq_zero _ p
      exact_mod_cast this
    rw [hQ, coeff_sub, c1, c2]
    linear_combination (-(((𝓦p p).preΨ' p).coeff (p * m))) * hpRp''
  have hV_coeff : V.coeff (3 * m + 3) = 4 := by
    have h2p : (2 : Rp p) ^ (p - 1) = 1 := by
      have := ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod p hp2)
      have e := congrArg (MvPolynomial.C (σ := Fin 5)) this
      rwa [map_pow, map_ofNat, map_one] at e
    have h4m : (4 : Rp p) ^ (m + 1) = 4 := by
      rw [pow_succ, show (4 : Rp p) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * m = p - 1 by omega, h2p, one_mul]
    have hidx : (3 * m + 3) * p = (m + 1) * 3 + 3 * k := by rw [hk_eq, hm]; ring
    have hSm1_deg : (S ^ (m + 1)).natDegree ≤ (m + 1) * 3 := natDegree_pow_le.trans (by rw [hSdeg3])
    have epow := coeff_pow_mul_natDegree S (m + 1)
    rw [hSdeg3, hS, leadingCoeff_Ψ₂Sq _ h4] at epow
    rw [hV, coeff_contract hp0, hidx, coeff_mul_add_eq_of_natDegree_le hSm1_deg hHb_deg, hHb_coeff, mul_one,
      hS, epow, h4m]
  have hF : (4 : Rp p) * ((𝓦p p).preΨ' p).coeff (p * m) = 4 * A := by
    have e := congrArg (fun q => q.coeff (3 + 3 * m)) hstar
    rw [coeff_mul_add_eq_of_natDegree_le hCf_deg hQ_deg, hCf_coeff, hQ_coeff, coeff_C_mul,
      show 3 + 3 * m = 3 * m + 3 by ring, hV_coeff, mul_comm A] at e
    exact e
  rw [hm1]
  exact mul_left_cancel₀ h4 hF

theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)
    (q : ℕ) : (W.map f).hasseInvariant q = f (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  rw [← Ψ₂Sq_eq, ← Ψ₂Sq_eq, map_Ψ₂Sq, ← Polynomial.map_pow, coeff_map]

theorem coeff_preΨ'_eq_hasseInvariant_of_UIdentity (hp2 : p ≠ 2) (hU : UIdentity 𝓦 p)
    (hcop : IsCoprime (((𝓦p p).map (algebraMap (Rp p) (Fp p))).Φ p)
      (((𝓦p p).map (algebraMap (Rp p) (Fp p))).ΨSq p))
    (hΨne : (𝓦p p).preΨ' p ≠ 0)
    {R : Type*} [CommRing R] [CharP R p] (W : WeierstrassCurve R) :
    (W.preΨ' p).coeff (p * ((p - 1) / 2)) = W.hasseInvariant p := by
  rw [← map_univHomP p W, map_preΨ', coeff_map, hasseInvariant_map,
    coeff_preΨ'_𝓦p_eq_hasseInvariant p hp2 hU hcop hΨne]

end S2
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

end WeierstrassCurve.Universal
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ ΨSq_ofNat a₃ a₁ natDegree_Ψ₂Sq_le natDegree_Φ preΨ'_ne_zero map preΨ'_two map_b₂ map_Φ b₂ Ψ₂Sq a₄ a₂ a₆ ofJ1728_Δ map_preΨ' reduction leadingCoeff_Ψ₂Sq coeff_preΨ' ofJ1728 preΨ' map_ΨSq ΨSq map_b₆ map_injective map_Δ Ψ₂Sq_eq b₆ Δ coeff_Φ natDegree_preΨ'_le natDegree_Ψ₂Sq leadingCoeff_Φ map_Ψ₂Sq j b₄ hasseInvariant Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq prePsi_ne_zero_of_isElliptic"
p2m_open "WeierstrassCurve"

open Universal

theorem Universal.preΨ'_𝓦p_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (𝓦p p).preΨ' p ≠ 0 := by
  intro h
  haveI := isElliptic_𝓦p_Fp p hp2
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hne := WeierstrassCurve.prePsi_ne_zero_of_isElliptic ((𝓦p p).map (algebraMap (Rp p) (Fp p))) hodd
  apply hne
  rw [map_preΨ', h, Polynomial.map_zero]

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve WeierstrassCurve.Universal in

theorem solution {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    [CharP R p] (W : WeierstrassCurve R) :
    (W.preΨ' p).coeff (p * ((p - 1) / 2)) = W.hasseInvariant p := by
  haveI := isElliptic_𝓦p_Fp p hp
  exact coeff_preΨ'_eq_hasseInvariant_of_UIdentity p hp (WeierstrassCurve.Psi2Sq_mul_wronskian_sq 𝓦 p)
    (WeierstrassCurve.isCoprime_Phi_PsiSq _ (p : ℤ)) (Universal.preΨ'_𝓦p_ne_zero p hp) W

end
p2m_reactivate "P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.WeierstrassCurve.Universal"

end S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant
end P2MW
export P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant (solution)
