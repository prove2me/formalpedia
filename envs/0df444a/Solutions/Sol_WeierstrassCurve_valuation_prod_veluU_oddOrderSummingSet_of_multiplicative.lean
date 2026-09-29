-- Prove2me | solution 1 for WeierstrassCurve.valuation_prod_veluU_oddOrderSummingSet_of_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3ab4883d-acaa-5d04-ae94-0afef65abd98

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_valuation_prod_veluU_oddOrderSummingSet_of_multiplicative
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
open WeierstrassCurve WeierstrassCurve.Affine ValuationSubring

namespace N5aux

section ValueGroup
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

private lemma pow_left_inj {a b : Γ} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hlt (zero_le' (a := a)) hn))
  · exact heq
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_left₀ hgt (zero_le' (a := b)) hn))

private lemma pow_right_inj_of_lt_one {a : Γ} (ha0 : a ≠ 0) (ha1 : a < 1)
    {m n : ℕ} (h : a ^ m = a ^ n) : m = n := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr ha0) ha1 hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr ha0) ha1 hgt))

end ValueGroup

variable {K : Type*} [Field K]

private lemma veluU_node_expand (W' : WeierstrassCurve K) {x y x₀ y₀ : K}
    (heq : W'.toAffine.Equation x y)
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄) :
    W'.veluU x y =
      -4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))
      + (W'.b₂ + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3 := by

  rw [W'.veluU_eq_Ψ₂Sq_eval heq]
  simp only [Ψ₂Sq, b₂, b₄, b₆, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination (-4 * x + 4 * x₀) * hFx + (2 * W'.a₁ * x - W'.a₁ * x₀ + 2 * y₀ + W'.a₃) * hFy

section ProdGlue
variable {F : Type*} [Field F] [DecidableEq F] (W' : WeierstrassCurve F)

private lemma coords_inj_on_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Set ℕ) := by
  intro k hk k' hk' hcoords
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'

  have hkne : k • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk.1 hd) (by omega)
  have hk'ne : k' • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k' := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk'.1 hd) (by omega)

  have hpt : k • Q = k' • Q := by
    cases hkQ : k • Q with
    | zero => exact absurd hkQ hkne
    | some xk yk hknon =>
      cases hk'Q : k' • Q with
      | zero => exact absurd hk'Q hk'ne
      | some xk' yk' hk'non =>
        simp only [hkQ, hk'Q, Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hcoords
        obtain ⟨rfl, rfl⟩ := hcoords
        rfl

  have hz : (p : ℤ) ∣ ((k : ℤ) - k') := by
    have h0 : ((k : ℤ) - k') • Q = 0 := by
      rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hpt]; exact sub_self _
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
    rw [hord] at this
    exact_mod_cast this
  have habs : |(k : ℤ) - (k' : ℤ)| < p := by
    have h1 : (k : ℤ) - k' < p := by omega
    have h2 : (k' : ℤ) - k < p := by omega
    rw [abs_sub_lt_iff]; omega
  have hsub0 : (k : ℤ) - k' = 0 := Int.eq_zero_of_abs_lt_dvd hz habs
  omega

private lemma prod_veluU_eq_prod_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    ∏ P ∈ W'.oddOrderSummingSet Q n, W'.veluU P.1 P.2
      = ∏ k ∈ Finset.Icc 1 n, W'.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 := by
  rw [oddOrderSummingSet, Finset.prod_image]
  intro k hk k' hk' h
  exact coords_inj_on_Icc W' hord hn (by simp only [Finset.coe_Icc]; exact Finset.mem_Icc.mp hk)
    (by simp only [Finset.coe_Icc]; exact Finset.mem_Icc.mp hk') h

end ProdGlue

section SubgroupGlue

open WeierstrassCurve.Affine.Point

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma zeroMem : W.InZeroComponentAt A 0 := Or.inl rfl

private lemma negMem {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (-P) := by
  exact W.inZeroComponentAt_sub A (zeroMem W A) hP

private lemma addMem {P Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) (hQ : W.InZeroComponentAt A Q) :
    W.InZeroComponentAt A (P + Q) := by
  simpa [sub_neg_eq_add] using W.inZeroComponentAt_sub A hP (negMem W A hQ)

private lemma nsmulMem (n : ℕ) {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (n • P) := by
  induction n with
  | zero => (have h__af := zeroMem W A; simp at h__af ⊢; exact h__af)
  | succ n ih => rw [succ_nsmul]; exact addMem W A ih hP

private lemma zsmulMem (a : ℤ) {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (a • P) := by
  cases a with
  | ofNat n => simpa using nsmulMem W A n hP
  | negSucc n => rw [negSucc_zsmul]; exact negMem W A (nsmulMem W A (n + 1) hP)

private lemma mem_of_nsmul_mem {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQ : p • Q = 0)
    {m : ℕ} (hm : ¬ p ∣ m) (h : W.InZeroComponentAt A (m • Q)) :
    W.InZeroComponentAt A Q := by
  have hcop : IsCoprime (m : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hm)
  obtain ⟨a, b, hab⟩ := hcop
  have hQeq : Q = a • (m • Q) := by
    calc Q = ((a * m + b * p : ℤ)) • Q := by rw [hab, one_zsmul]
    _ = a • (m • Q) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, hQ]
        rw [zsmul_zero, add_zero]
  rw [hQeq]; exact zsmulMem W A a h

private lemma mem_of_nsmul_mem' {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQ : p • Q = 0) :
    ∀ m : ℕ, 0 < m → m < p → W.InZeroComponentAt A (m • Q) → W.InZeroComponentAt A Q :=
  fun _ hm1 hmp h => mem_of_nsmul_mem W A hp hQ (Nat.not_dvd_of_pos_of_lt hm1 hmp) h

end SubgroupGlue

section ToricEngine

open WeierstrassCurve.Affine.Point

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma unpack_torsion {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hℓp : ℓ ≠ p)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQord : addOrderOf Q = p)
    {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      k • Q = .some x y h ∧ x ∈ A ∧ y ∈ A := by
  have hk0 : k • Q ≠ 0 := by
    intro h0
    have hdvd : p ∣ k := by
      rw [← hQord]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hk1 hkp)
  have htor : p • (k • Q) = 0 := by
    rw [smul_comm, ← hQord, addOrderOf_nsmul_eq_zero, smul_zero]
  have hnd : ¬ ℓ ∣ p := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)
  rcases W.torsion_integral_of_not_dvd hℓ A hA hnd (k • Q) htor with h0 | ⟨x, y, h, heq, hx, hy⟩
  · exact absurd h0 hk0
  · exact ⟨x, y, h, heq, hx, hy⟩

private lemma residue_nonsingular_of_mem {x y : AlgebraicClosure ℚ}
    {h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y}
    (hx : x ∈ A) (hy : y ∈ A) (hmem : W.InZeroComponentAt A (.some x y h)) :
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
      (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by
  rcases hmem with h0 | ⟨x', y', h', heq, hcase⟩
  · exact absurd h0 (some_ne_zero h)
  · obtain ⟨hx', hy'⟩ : x = x' ∧ y = y' := by
      have := heq
      rw [Point.some.injEq] at this
      exact ⟨this.1, this.2⟩
    subst hx'; subst hy'
    rcases hcase with hnx | ⟨hx'', hy'', hns⟩
    · exact absurd hx hnx
    · exact hns

private lemma valuation_veluU_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : AlgebraicClosure ℚ}
    {h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y}
    (hx : x ∈ A) (hy : y ∈ A)
    (hmem : W.InZeroComponentAt A (.some x y h))
    (htor : p • (Point.some x y h) = 0) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluU x y) = 1 := by
  classical
  obtain ⟨red, hred0, hredadd, hredint, hredinf, hredker, hredgal⟩ :=
    W.exists_reduction_inZeroComponentAt A
  have hns := residue_nonsingular_of_mem W A hx hy hmem
  set xb := IsLocalRing.residue A ⟨x, hx⟩ with hxb
  set yb := IsLocalRing.residue A ⟨y, hy⟩ with hyb
  have hredP : red (.some x y h) = .some xb yb hns := hredint x y h hx hy hns
  have hrednsmul : ∀ n : ℕ, red (n • (.some x y h)) = n • red (.some x y h) := by
    intro n
    induction n with
    | zero => simpa using hred0
    | succ n ih =>
      calc red ((n + 1) • (.some x y h))
          = red (n • (.some x y h) + (.some x y h)) := by rw [succ_nsmul]
        _ = red (n • (.some x y h)) + red (.some x y h) :=
            hredadd _ _ (nsmulMem W A n hmem) hmem
        _ = n • red (.some x y h) + red (.some x y h) := by rw [ih]
        _ = (n + 1) • red (.some x y h) := (succ_nsmul _ n).symm
  have hptor : p • (Point.some xb yb hns) = 0 := by
    have hh := hrednsmul p
    rw [htor, hred0, hredP] at hh
    exact hh.symm

  have hga1 : ((W.a₁ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A W.a₁
  have hga3 : ((W.a₃ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A W.a₃
  set gA : A := 2 * ⟨y, hy⟩ + ⟨_, hga1⟩ * ⟨x, hx⟩ + ⟨_, hga3⟩ with hgA
  have hgA_coe : (gA : AlgebraicClosure ℚ)
      = 2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + (W.a₃ : AlgebraicClosure ℚ) := rfl
  have hres_g : IsLocalRing.residue A gA
      = 2 * yb + (W.a₁ : IsLocalRing.ResidueField A) * xb
        + (W.a₃ : IsLocalRing.ResidueField A) := by
    have e1 : (⟨_, hga1⟩ : A) = (W.a₁ : A) := by ext; simp
    have e3 : (⟨_, hga3⟩ : A) = (W.a₃ : A) := by ext; simp
    rw [hgA, e1, e3]
    simp [map_add, map_mul, map_intCast, map_ofNat, hxb, hyb]
  by_cases hcase : IsLocalRing.residue A gA = 0
  · exfalso
    have hYeq : yb = (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.negY xb yb := by
      have hz : 2 * yb + (W.a₁ : IsLocalRing.ResidueField A) * xb
          + (W.a₃ : IsLocalRing.ResidueField A) = 0 := by rw [← hres_g]; exact hcase
      simp only [Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast]
      linear_combination hz
    have h2tor : Point.some xb yb hns + Point.some xb yb hns = 0 := add_self_of_Y_eq hYeq
    have hord2 : addOrderOf (Point.some xb yb hns) ∣ 2 := by
      rw [addOrderOf_dvd_iff_nsmul_eq_zero, two_nsmul]; exact h2tor
    have hordp : addOrderOf (Point.some xb yb hns) ∣ p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hptor
    have hord1 : addOrderOf (Point.some xb yb hns) = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hord2 hordp)
    exact some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp hord1)
  · have hnotmax : gA ∉ IsLocalRing.maximalIdeal A := fun hmax =>
      hcase ((IsLocalRing.residue_eq_zero_iff _).mpr hmax)
    have hvg : A.valuation gA = 1 := by
      rcases A.valuation_lt_one_or_eq_one gA with hlt | heq
      · exact absurd ((A.valuation_lt_one_iff gA).mpr hlt) hnotmax
      · exact heq
    have hcoeff1 : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁
        = (W.a₁ : AlgebraicClosure ℚ) := by
      simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, eq_intCast, map_intCast]
    have hcoeff3 : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃
        = (W.a₃ : AlgebraicClosure ℚ) := by
      simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
    have hval_u : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluU x y
        = (-(gA : AlgebraicClosure ℚ)) ^ 2 := by
      simp only [veluU, veluGy, hcoeff1, hcoeff3, hgA_coe]
    rw [hval_u, map_pow, Valuation.map_neg, hvg, one_pow]

private lemma valuation_prod_veluU_of_inZeroComponentAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓp : ℓ ≠ p)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQord : addOrderOf Q = p)
    (hmem : W.InZeroComponentAt A Q) :
    A.valuation (∏ k ∈ Finset.Icc 1 (p / 2),
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluU
        (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) = 1 := by
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k hk
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hkp : k < p := lt_of_le_of_lt hkn (Nat.div_lt_self hp.pos one_lt_two)
  obtain ⟨x, y, h, heq, hx, hy⟩ := unpack_torsion W A hℓ hA hp hℓp hQord hk1 hkp
  have hkmem : W.InZeroComponentAt A (k • Q) := nsmulMem W A k hmem
  have hktor : p • (k • Q) = 0 := by
    rw [smul_comm, ← hQord, addOrderOf_nsmul_eq_zero, smul_zero]
  rw [heq] at hkmem hktor ⊢
  simp only [coordsOrZero_some]
  exact valuation_veluU_eq_one W A hp hp2 hx hy hkmem hktor

end ToricEngine

section NontoricEngine

local notation "Kb" => AlgebraicClosure ℚ

private theorem veluU_expand (W : WeierstrassCurve ℤ) {x₀ y₀ x y : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).veluU x y =
      -4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        + ((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3 := by
  rw [Affine.equation_iff] at h
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast] at h
  simp only [veluU, veluGy, Affine.baseChange_a₁, Affine.baseChange_a₃, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
  have hb₂ : ((W.b₂ : ℤ) : Kb) = (W.a₁ : Kb) ^ 2 + 4 * W.a₂ := by simp [WeierstrassCurve.b₂]
  rw [hb₂]
  linear_combination 4 * h + (2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ + 2 * W.a₁ * (x - x₀)) * hFy
    - 4 * (x - x₀) * hFx

private theorem valuation_veluU_eq (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)
    {x₀ y₀ x y : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluU x y) = A.valuation (x - x₀) ^ 2 := by
  rw [veluU_expand W hFy hFx h]
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have hX0 : A.valuation (x - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  have hsq : A.valuation (((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2) = A.valuation (x - x₀) ^ 2 := by
    rw [map_mul, map_pow, hnode, one_mul]
  have hε : A.valuation (-4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
      < A.valuation (((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2) := by
    rw [hsq, map_mul, Valuation.map_neg]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) hsh
  have hcube : A.valuation (4 * (x - x₀) ^ 3)
      < A.valuation (-4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        + ((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2) := by
    rw [Valuation.map_add_eq_of_lt_right _ hε, hsq, map_mul, map_pow]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h4) ?_
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hX0) hX (by norm_num)
  rw [Valuation.map_add_eq_of_lt_left _ hcube, Valuation.map_add_eq_of_lt_right _ hε, hsq]

private theorem node_equation (W : WeierstrassCurve ℤ) {x₀ y₀ x y : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y) :
    (y - y₀) ^ 2 + (W.a₁ : Kb) * (x - x₀) * (y - y₀)
      = (3 * x₀ + W.a₂) * (x - x₀) ^ 2 + (x - x₀) ^ 3
        - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  rw [Affine.equation_iff] at h
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast] at h
  linear_combination h - (y - y₀) * hFy - (x - x₀) * hFx

private theorem valuation_slope_le_one (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)
    {x₀ y₀ x y : Kb} (hx₀ : x₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    A.valuation ((y - y₀) / (x - x₀)) ≤ 1 := by
  have hX0 : A.valuation (x - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  suffices hYX : A.valuation (y - y₀) ≤ A.valuation (x - x₀) by
    rw [map_div₀]
    exact div_le_one_of_le₀ hYX zero_le'
  by_contra hlt
  rw [not_le] at hlt
  have hY0 : 0 < A.valuation (y - y₀) := lt_of_le_of_lt zero_le' hlt
  have key := congrArg A.valuation (node_equation W hFy hFx h)

  have ha₁ : A.valuation (W.a₁ : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hcross : A.valuation ((W.a₁ : Kb) * (x - x₀) * (y - y₀)) < A.valuation ((y - y₀) ^ 2) := by
    rw [map_mul, map_mul, map_pow, pow_two]
    calc A.valuation (W.a₁ : Kb) * A.valuation (x - x₀) * A.valuation (y - y₀)
        ≤ A.valuation (x - x₀) * A.valuation (y - y₀) := by
          rw [mul_assoc]; exact mul_le_of_le_one_left' ha₁
      _ < A.valuation (y - y₀) * A.valuation (y - y₀) := (mul_lt_mul_iff_left₀ hY0).mpr hlt
  have hlhs : A.valuation ((y - y₀) ^ 2 + (W.a₁ : Kb) * (x - x₀) * (y - y₀))
      = A.valuation (y - y₀) ^ 2 := by
    rw [Valuation.map_add_eq_of_lt_left _ hcross, map_pow]

  have hXY2 : A.valuation (x - x₀) ^ 2 < A.valuation (y - y₀) ^ 2 :=
    pow_lt_pow_left₀ hlt zero_le' two_ne_zero
  have h3x₀ : A.valuation (3 * x₀ + (W.a₂ : Kb)) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (add_mem (mul_mem (ofNat_mem A 3) hx₀) (intCast_mem A _))
  have hr1 : A.valuation ((3 * x₀ + (W.a₂ : Kb)) * (x - x₀) ^ 2) < A.valuation (y - y₀) ^ 2 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h3x₀) hXY2
  have hr2 : A.valuation ((x - x₀) ^ 3) < A.valuation (y - y₀) ^ 2 := by
    rw [map_pow]
    exact lt_trans (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hX0) hX (by norm_num)) hXY2
  have hr3 : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (y - y₀) ^ 2 :=
    lt_trans hsh hXY2
  have hrhs := Valuation.map_sub_lt A.valuation (Valuation.map_add_lt A.valuation hr1 hr2) hr3
  rw [← key, hlhs] at hrhs
  exact lt_irrefl _ hrhs

private theorem branch_dichotomy (A : ValuationSubring Kb) {s₁ s₂ : Kb}
    (h₁ : A.valuation s₁ ≤ 1) (h₂ : A.valuation s₂ ≤ 1) :
    A.valuation (s₁ - s₂) < 1 ∨ A.valuation (s₁ - s₂) = 1 :=
  (Valuation.map_sub_le A.valuation h₁ h₂).lt_or_eq

private theorem sum_eq_sum_id_of_injOn {n : ℕ} (j : ℕ → ℕ)
    (hmem : ∀ k ∈ Finset.Icc 1 n, j k ∈ Finset.Icc 1 n) (hinj : Set.InjOn j (Finset.Icc 1 n)) :
    ∑ k ∈ Finset.Icc 1 n, j k = ∑ i ∈ Finset.Icc 1 n, i := by
  have himg : (Finset.Icc 1 n).image j = Finset.Icc 1 n := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact hmem k hk
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image (f := fun i => i) hinj, himg]

private theorem eight_mul_sum_Icc (n : ℕ) :
    8 * ∑ i ∈ Finset.Icc 1 n, i = (2 * n + 1) ^ 2 - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    have h1 : 1 ≤ (2 * n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (2 * (n + 1) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring

private theorem valuation_prod_veluU_pow_of_not_inZeroComponentAt
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring Kb) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point) (hQord : addOrderOf Q = p)
    (hcl : ∀ m : ℕ, 0 < m → m < p → W.InZeroComponentAt A (m • Q) → W.InZeroComponentAt A Q)
    (hout : ¬ W.InZeroComponentAt A Q) :
    A.valuation (∏ k ∈ Finset.Icc 1 (p / 2),
        ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
          ^ (4 * p)
      = A.valuation (W.Δ : Kb) ^ (p ^ 2 - 1) := by

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hℓ hΔ hℓΔ hℓc₄ A hA
  have hΔε := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
    W A hx₀ hy₀ hFy hFx hnode hbad
  set n := p / 2 with hn
  have hpn : p = 2 * n + 1 := (Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)).symm
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q

  have hpt : ∀ k ∈ Finset.Icc 1 n, ∃ (x y : Kb)
      (hxy : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y), k • Q = .some x y hxy := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hne : k • Q ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQord]; omega)
    cases hkQ : k • Q with
    | zero => exact absurd hkQ hne
    | @some x y hxy => exact ⟨x, y, hxy, rfl⟩
  choose! xk yk hk hkQ using hpt

  have hlev : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1 := by
    intro k hk'
    have hk2 := hk'
    rw [Finset.mem_Icc] at hk2
    refine (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx
      hnode hbad (hk k hk')).mp ?_
    have hout' : ¬ W.InZeroComponentAt A (k • Q) :=
      fun hin => hout (hcl k (by omega) (by omega) hin)
    rw [hkQ k hk'] at hout'
    exact hout'

  have hrow : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (W.Δ : Kb) < A.valuation (xk k - x₀) ^ 2 ∧
        ∃ j : ℕ, 1 ≤ j ∧ 2 * j < p ∧ A.valuation (xk k - x₀) ^ p = A.valuation (W.Δ : Kb) ^ j := by
    intro k hk'
    have htor : p • (Point.some (xk k) (yk k) (hk k hk')) = 0 := by
      have h0 : p • (k • Q) = 0 := by rw [← mul_nsmul', mul_comm, mul_nsmul', hpQ, nsmul_zero]
      rw [hkQ k hk'] at h0
      exact h0
    exact WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt W hℓ hΔ
      hℓΔ hℓc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 (hk k hk') htor (hlev k hk')
  have hsh : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2 := by
    intro k hk'
    rw [← hΔε]
    exact (hrow k hk').1
  choose! j hj1 hj2 hjpow using fun k hk' => (hrow k hk').2

  have hprod : A.valuation (∏ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
        = ∏ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) ^ 2 := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun k hk' => ?_
    rw [hkQ k hk', Point.coordsOrZero_some]
    exact valuation_veluU_eq W A hFy hFx hnode (hk k hk').left (hlev k hk') (hsh k hk')

  have hslope : ∀ k ∈ Finset.Icc 1 n, A.valuation ((yk k - y₀) / (xk k - x₀)) ≤ 1 :=
    fun k hk' => valuation_slope_le_one W A hx₀ hFy hFx (hk k hk').left (hlev k hk') (hsh k hk')
  have hinj : Set.InjOn j (Finset.Icc 1 n) := by
    intro k hkm k' hkm' hjj
    have hk2 := Finset.mem_coe.mp hkm
    have hk2' := Finset.mem_coe.mp hkm'
    have hkI := hk2
    have hkI' := hk2'
    rw [Finset.mem_Icc] at hkI hkI'
    have hveq : A.valuation (xk k - x₀) = A.valuation (xk k' - x₀) := by
      rw [← pow_left_inj₀ zero_le' zero_le' hp.ne_zero, hjpow k hk2, hjpow k' hk2', hjj]
    by_contra hne
    rcases branch_dichotomy A (hslope k hk2) (hslope k' hk2') with hbr | hbr
    ·
      have hz : W.InZeroComponentAt A (k • Q - k' • Q) := by
        rw [hkQ k hk2, hkQ k' hk2']
        exact (WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq W A hx₀ hy₀
          hFy hFx hnode hbad (hk k hk2) (hk k' hk2') (hlev k hk2) (hlev k' hk2') hveq
          (hsh k hk2) hbr).1
      rcases lt_or_gt_of_ne hne with hlt | hlt
      ·
        have hz' := WeierstrassCurve.inZeroComponentAt_sub W A (P := 0) (Or.inl rfl) hz
        rw [zero_sub, neg_sub, sub_eq_add_neg, ← sub_nsmul Q hlt.le] at hz'
        exact hout (hcl (k' - k) (by omega) (by omega) hz')
      · have hz' : W.InZeroComponentAt A ((k - k') • Q) := by
          rw [sub_nsmul Q hlt.le, ← sub_eq_add_neg]; exact hz
        exact hout (hcl (k - k') (by omega) (by omega) hz')
    ·
      have hz : W.InZeroComponentAt A ((k + k') • Q) := by
        rw [add_nsmul, hkQ k hk2, hkQ k' hk2']
        exact (WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne W A hx₀ hy₀
          hFy hFx hnode hbad (hk k hk2) (hk k' hk2') (hlev k hk2) (hlev k' hk2') hveq
          (hsh k hk2) hbr).1
      exact hout (hcl (k + k') (by omega) (by omega) hz)

  have hmem : ∀ k ∈ Finset.Icc 1 n, j k ∈ Finset.Icc 1 n := by
    intro k hk'
    rw [Finset.mem_Icc]
    exact ⟨hj1 k hk', by have := hj2 k hk'; omega⟩
  have hsum : 8 * ∑ k ∈ Finset.Icc 1 n, j k = p ^ 2 - 1 := by
    rw [sum_eq_sum_id_of_injOn j hmem hinj, eight_mul_sum_Icc, hpn]

  rw [hprod, ← Finset.prod_pow, ← hsum, mul_comm 8, Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k hk' => ?_
  rw [← pow_mul, show 2 * (4 * p) = p * 8 by ring, pow_mul, hjpow k hk', ← pow_mul]

end NontoricEngine

end N5aux

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓp : ℓ ≠ p)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p) :
    let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
    let S := Wb.oddOrderSummingSet Q (p / 2)
    (W.InZeroComponentAt A Q →
      A.valuation (∏ P ∈ S, Wb.veluU P.1 P.2) = 1) ∧
    (¬ W.InZeroComponentAt A Q →
      A.valuation (∏ P ∈ S, Wb.veluU P.1 P.2) ^ (4 * p)
        = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ (p ^ 2 - 1)) := by

  intro Wb S
  set n := p / 2 with hn_def
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp2n : p = 2 * n + 1 := by
    obtain ⟨m, hm⟩ := hpodd; omega
  have h2np : 2 * n < p := by omega
  have hn1 : 1 ≤ n := by
    have : 3 ≤ p := hp.two_le.lt_of_ne' hp2 |>.nat_succ_le
    omega
  refine ⟨fun hQ0 => ?_, fun hQ0 => ?_⟩
  ·
    have h2np' : 2 * (p / 2) < p := by omega
    simp only [S, Wb]
    rw [N5aux.prod_veluU_eq_prod_Icc _ hQord h2np']
    exact N5aux.valuation_prod_veluU_of_inZeroComponentAt W A hℓ hA hp hp2 hℓp hQord hQ0
  ·
    have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
    have h2np' : 2 * (p / 2) < p := by omega
    simp only [S, Wb]
    rw [N5aux.prod_veluU_eq_prod_Icc _ hQord h2np']
    exact N5aux.valuation_prod_veluU_pow_of_not_inZeroComponentAt W hΔ hℓ hℓΔ hℓc₄ A hA hp hp2 Q
      hQord (N5aux.mem_of_nsmul_mem' W A hp hpQ) hQ0

end S_WeierstrassCurve_valuation_prod_veluU_oddOrderSummingSet_of_multiplicative
end P2MW
export P2MW.S_WeierstrassCurve_valuation_prod_veluU_oddOrderSummingSet_of_multiplicative (solution)
