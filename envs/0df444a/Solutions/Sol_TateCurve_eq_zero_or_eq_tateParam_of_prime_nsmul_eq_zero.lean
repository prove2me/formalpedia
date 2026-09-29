-- Prove2me | solution 1 for TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4ec82729-b1ba-5b15-847c-113fa3c462ed

import Mathlib
import Definitions.Def_TateCurve_XMultDistinctRouteB
import Definitions.Def_TateCurve_TateFiltrationPrep
import Theorems.Thm_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine mk.injEq map mk toAffine ψ₂ j card_p_torsion_le_of_natCast_ne_zero finite_p_torsion_of_natCast_ne_zero"
p2m_open "WeierstrassCurve"
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

private abbrev _root_.WeierstrassCurve.n_torsionGen (n : ℕ) : Type _ := Submodule.torsionBy ℤ W.toAffine.Point n
p2m_export "WeierstrassCurve" "n_torsionGen"
end WeierstrassCurve

open WeierstrassCurve.Affine
open Polynomial

namespace TateCurve
p2m_export "TateCurve" "nsmul_prime_eq_zero eq_zpow_mul_of_pointXY_eq SymAddHyps nonsingular_point OffLattice AddParams pointX pointY curve Δ_ne_zero map_pointX_eq_self map_pointY_eq_self"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q ζ t : K}

section LatticeHelpers

private lemma zpow_ne_one_of_norm_lt_one (hq : ‖q‖₊ < 1) {m : ℤ} (hm : m ≠ 0) :
    q ^ m ≠ 1 := by

  have hpos : ∀ n : ℕ, n ≠ 0 → q ^ n ≠ 1 := by
    intro n hn hcontra
    have h1 : ‖q ^ n‖₊ = 1 := by rw [hcontra, nnnorm_one]
    have h2 : ‖q ^ n‖₊ < 1 := by
      rw [nnnorm_pow]
      exact pow_lt_one₀ zero_le hq hn
    exact absurd h1 (ne_of_lt h2)
  intro hcontra
  rcases lt_trichotomy m 0 with hneg | hzero | hpos'
  ·
    have h1 : q ^ (-m) = 1 := by
      have h2 : (q ^ m)⁻¹ = (1 : K)⁻¹ := by rw [hcontra]
      rwa [← zpow_neg, inv_one] at h2
    have h2 : q ^ ((-m).toNat) = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      exact h1
    exact hpos (-m).toNat (by omega) h2
  · exact hm hzero
  · have h2 : q ^ (m.toNat) = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      exact hcontra
    exact hpos m.toNat (by omega) h2

private lemma zpow_left_injective_of_norm_lt_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {m n : ℤ}
    (h : q ^ m = q ^ n) : m = n := by
  by_contra hmn
  apply zpow_ne_one_of_norm_lt_one hq (sub_ne_zero.mpr hmn)
  rw [sub_eq_add_neg, zpow_add₀ hq0, h, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero]

end LatticeHelpers

section TateParameters

variable {p : ℕ}

lemma tateParam_ne_zero (hζ0 : ζ ≠ 0) (ht0 : t ≠ 0) {i j : ℕ} : ζ ^ i * t ^ j ≠ 0 :=
  mul_ne_zero (pow_ne_zero i hζ0) (pow_ne_zero j ht0)

lemma tateParam_pow (hζp : ζ ^ p = 1) (ht : t ^ p = q) (i j : ℕ) :
    (ζ ^ i * t ^ j) ^ p = q ^ (j : ℤ) := by
  have h1 : (ζ ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have h2 : (t ^ j) ^ p = q ^ j := by rw [← pow_mul, mul_comm, pow_mul, ht]
  rw [mul_pow, h1, h2, one_mul, zpow_natCast]

lemma tateParam_offLattice (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : ¬(i = 0 ∧ j = 0)) :
    OffLattice q (ζ ^ i * t ^ j) := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  intro n hn

  have h1 : q ^ (n * (p : ℤ) + (j : ℤ)) = 1 := by
    have h2 : (q ^ n * (ζ ^ i * t ^ j)) ^ p = 1 := by rw [hn, one_pow]
    rwa [mul_pow, tateParam_pow hζp ht, ← zpow_natCast (q ^ n) p, ← zpow_mul,
      ← zpow_add₀ hq0] at h2

  have h3 : n * (p : ℤ) + (j : ℤ) = 0 := by
    by_contra h
    exact zpow_ne_one_of_norm_lt_one hq h h1

  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | h0 | hpos
    · exfalso
      have hle : n * (p : ℤ) ≤ (-1) * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
      omega
    · exact h0
    · exfalso
      have hle : 1 * (p : ℤ) ≤ n * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
      omega
  have hj0 : j = 0 := by
    have h4 : (j : ℤ) = 0 := by
      rw [hn0] at h3
      simpa using h3
    exact_mod_cast h4

  have hi0 : i ≠ 0 := fun h => hij ⟨h, hj0⟩
  have h5 : ζ ^ i = 1 := by
    have h6 := hn
    rw [hn0, zpow_zero, one_mul, hj0, pow_zero, mul_one] at h6
    exact h6
  exact hi0 (hζ.pow_inj hi (by omega) (by rw [h5, pow_zero]))

lemma tateParam_class_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (ht0 : t ≠ 0)
    {i j i' j' : ℕ} (hi : i < p) (hj : j < p) (hi' : i' < p) (hj' : j' < p)
    {k : ℤ} (hk : ζ ^ i' * t ^ j' = q ^ k * (ζ ^ i * t ^ j)) : i = i' ∧ j = j' := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one

  have hpow : (q : K) ^ (j' : ℤ) = q ^ (k * (p : ℤ) + (j : ℤ)) := by
    have h1 : (ζ ^ i' * t ^ j') ^ p = (q ^ k * (ζ ^ i * t ^ j)) ^ p := by rw [hk]
    rwa [tateParam_pow hζp ht, mul_pow, tateParam_pow hζp ht, ← zpow_natCast (q ^ k) p,
      ← zpow_mul, ← zpow_add₀ hq0] at h1
  have hjj : (j' : ℤ) = k * (p : ℤ) + (j : ℤ) :=
    zpow_left_injective_of_norm_lt_one hq0 hq hpow

  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hneg | h0 | hpos
    · exfalso
      have hle : k * (p : ℤ) ≤ (-1) * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
      omega
    · exact h0
    · exfalso
      have hle : 1 * (p : ℤ) ≤ k * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
      omega
  have hjeq : j = j' := by
    have h4 : (j' : ℤ) = (j : ℤ) := by rw [hjj, hk0]; ring
    exact_mod_cast h4.symm

  have hieq : i = i' := by
    have h2 : ζ ^ i' * t ^ j = ζ ^ i * t ^ j := by
      have h3 := hk
      rw [hk0, zpow_zero, one_mul, ← hjeq] at h3
      exact h3
    have h4 : ζ ^ i' = ζ ^ i := mul_right_cancel₀ (pow_ne_zero j ht0) h2
    exact hζ.pow_inj hi hi' h4.symm
  exact ⟨hieq, hjeq⟩

end TateParameters

section CMin

variable {p : ℕ}

private theorem coords_eq_tateParam_of_prime_nsmul_eq_zero
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {x y : K} (hns : (curve q).toAffine.Nonsingular x y)
    (hR : p • (Point.some x y hns : (curve q).toAffine.Point) = 0) :
    ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧
      x = pointX q (ζ ^ i * t ^ j) ∧ y = pointY q (ζ ^ i * t ^ j) := by
  classical

  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have ht0 : t ≠ 0 := by
    intro h0
    exact hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  haveI : (curve q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (Δ_ne_zero hq0 hq)⟩
  haveI : Finite ((curve q).n_torsionGen p) :=
    WeierstrassCurve.finite_p_torsion_of_natCast_ne_zero (W := curve q) hp hp5 hpK

  set par : ℕ → ℕ → (curve q).toAffine.Point := fun i j =>
    if hij : i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) then
      Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j))
        (nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0)
          (tateParam_offLattice hq0 hq hζ ht hij.1 hij.2.1 hij.2.2))
    else 0 with hpar

  have hpar_pos : ∀ {i j : ℕ} (hi : i < p) (hj : j < p) (hij : ¬(i = 0 ∧ j = 0)),
      par i j = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j))
        (nonsingular_point hq0 hq (tateParam_ne_zero hζ0 ht0)
          (tateParam_offLattice hq0 hq hζ ht hi hj hij)) := by
    intro i j hi hj hij
    simp only [hpar]
    rw [dif_pos ⟨hi, hj, hij⟩]
  have hpar_zero : ∀ {i j : ℕ}, (i = 0 ∧ j = 0) → par i j = 0 := by
    intro i j hij
    simp only [hpar]
    rw [dif_neg (fun h => h.2.2 hij)]

  have hpar_mem : ∀ i j : ℕ, par i j ∈ Submodule.torsionBy ℤ (curve q).toAffine.Point p := by
    intro i j
    by_cases hij : i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0)
    · rw [hpar_pos hij.1 hij.2.1 hij.2.2, Submodule.mem_torsionBy_iff, natCast_zsmul]
      exact nsmul_prime_eq_zero hyps hq0 hq (tateParam_ne_zero hζ0 ht0)
        (tateParam_offLattice hq0 hq hζ ht hij.1 hij.2.1 hij.2.2)
        (tateParam_pow hζp ht i j) hp hodd _
    ·

      simp only [hpar]
      rw [dif_neg hij]
      exact Submodule.zero_mem _

  let f : Fin p × Fin p → (curve q).n_torsionGen p :=
    fun ij => ⟨par (ij.1 : ℕ) (ij.2 : ℕ), hpar_mem _ _⟩

  have hf_inj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hff
    have hpp : par (i : ℕ) (j : ℕ) = par (i' : ℕ) (j' : ℕ) := congrArg Subtype.val hff
    by_cases hij : (i : ℕ) = 0 ∧ (j : ℕ) = 0
    · by_cases hij' : (i' : ℕ) = 0 ∧ (j' : ℕ) = 0
      ·
        rw [Prod.mk.injEq]
        exact ⟨Fin.ext (hij.1.trans hij'.1.symm), Fin.ext (hij.2.trans hij'.2.symm)⟩
      ·
        rw [hpar_zero hij, hpar_pos i'.isLt j'.isLt hij'] at hpp
        exact absurd hpp.symm (Point.some_ne_zero _)
    · by_cases hij' : (i' : ℕ) = 0 ∧ (j' : ℕ) = 0
      · rw [hpar_pos i.isLt j.isLt hij, hpar_zero hij'] at hpp
        exact absurd hpp (Point.some_ne_zero _)
      ·
        rw [hpar_pos i.isLt j.isLt hij, hpar_pos i'.isLt j'.isLt hij',
          Point.some.injEq] at hpp
        obtain ⟨hX, hY⟩ := hpp
        obtain ⟨k, hk⟩ := eq_zpow_mul_of_pointXY_eq hyps hq0 hq
          (tateParam_ne_zero hζ0 ht0) (tateParam_ne_zero hζ0 ht0)
          (tateParam_offLattice hq0 hq hζ ht i.isLt j.isLt hij)
          (tateParam_offLattice hq0 hq hζ ht i'.isLt j'.isLt hij')
          (tateParam_pow hζp ht (i : ℕ) (j : ℕ)) (tateParam_pow hζp ht (i' : ℕ) (j' : ℕ))
          hp hodd hX hY
        obtain ⟨hii, hjj⟩ := tateParam_class_eq hq0 hq hζ ht ht0
          i.isLt j.isLt i'.isLt j'.isLt hk
        rw [Prod.mk.injEq]
        exact ⟨Fin.ext hii, Fin.ext hjj⟩

  have hcard_le : Nat.card ((curve q).n_torsionGen p) ≤ p ^ 2 :=
    WeierstrassCurve.card_p_torsion_le_of_natCast_ne_zero (W := curve q) hp hp5 hpK
  have hcard_source : Nat.card (Fin p × Fin p) = p ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, sq]
  have hcard_ge : p ^ 2 ≤ Nat.card ((curve q).n_torsionGen p) := by
    have h := Nat.card_le_card_of_injective f hf_inj
    rwa [hcard_source] at h
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf_inj, by rw [hcard_source]; exact (le_antisymm hcard_le hcard_ge).symm⟩

  have hmemR : (Point.some x y hns : (curve q).toAffine.Point)
      ∈ Submodule.torsionBy ℤ (curve q).toAffine.Point p := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact hR
  obtain ⟨⟨i, j⟩, hfij⟩ := hbij.surjective ⟨Point.some x y hns, hmemR⟩
  have hpp : par (i : ℕ) (j : ℕ) = Point.some x y hns := congrArg Subtype.val hfij
  by_cases hij : (i : ℕ) = 0 ∧ (j : ℕ) = 0
  · rw [hpar_zero hij] at hpp
    exact absurd hpp.symm (Point.some_ne_zero _)
  · rw [hpar_pos i.isLt j.isLt hij, Point.some.injEq] at hpp
    exact ⟨(i : ℕ), (j : ℕ), i.isLt, j.isLt, hij, hpp.1.symm, hpp.2.symm⟩

private theorem eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero_aux
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (R : (curve q).toAffine.Point) (hR : p • R = 0) :
    R = 0 ∨ ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧
      ∃ hns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j))
        (pointY q (ζ ^ i * t ^ j)),
        R = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) hns := by
  rcases R with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · right
    obtain ⟨i, j, hi, hj, hij, hx, hy⟩ :=
      coords_eq_tateParam_of_prime_nsmul_eq_zero hyps hq0 hq hp hp5 hζ ht h hR
    subst hx
    subst hy
    exact ⟨i, j, hi, hj, hij, h, rfl⟩

end CMin

section InertiaBridge

variable {p : ℕ}

private theorem map_coords_eq_self_of_prime_nsmul_eq_zero
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (σ : K →+* K) (hσ : Isometry ⇑σ) (hσq : σ q = q) (hσζ : σ ζ = ζ) (hσt : σ t = t)
    {x y : K} (hns : (curve q).toAffine.Nonsingular x y)
    (hR : p • (Point.some x y hns : (curve q).toAffine.Point) = 0) :
    σ x = x ∧ σ y = y := by
  obtain ⟨i, j, hi, hj, hij, hx, hy⟩ :=
    coords_eq_tateParam_of_prime_nsmul_eq_zero hyps hq0 hq hp hp5 hζ ht hns hR
  have hζ0 : ζ ≠ 0 := by
    intro h0
    have hζp : ζ ^ p = 1 := hζ.pow_eq_one
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have ht0 : t ≠ 0 := by
    intro h0
    exact hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
  have hw0 : ζ ^ i * t ^ j ≠ 0 := tateParam_ne_zero hζ0 ht0
  have hσw : σ (ζ ^ i * t ^ j) = ζ ^ i * t ^ j := by
    rw [map_mul, map_pow, map_pow, hσζ, hσt]
  subst hx
  subst hy
  exact ⟨map_pointX_eq_self σ hσ hσq hσw hq0 hq hw0,
    map_pointY_eq_self σ hσ hσq hσw hq0 hq hw0⟩

private theorem map_coords_eq_self_of_prime_zsmul_eq_zero_aux
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (σ : K →+* K) (hσ : Isometry ⇑σ) (hσq : σ q = q) (hσζ : σ ζ = ζ) (hσt : σ t = t)
    {x y : K} (hns : (curve q).toAffine.Nonsingular x y)
    (hR : (p : ℤ) • (Point.some x y hns : (curve q).toAffine.Point) = 0) :
    σ x = x ∧ σ y = y :=
  map_coords_eq_self_of_prime_nsmul_eq_zero hyps hq0 hq hp hp5 hζ ht σ hσ hσq hσζ hσt hns
    (by rwa [natCast_zsmul] at hR)

end InertiaBridge

end TateCurve

p2m_open "WeierstrassCurve.Affine TateCurve P2MW.S_TateCurve_eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero.TateCurve"
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] {q ζ t : K} {p : ℕ}
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (R : (curve q).toAffine.Point) (hR : p • R = 0) :
    R = 0 ∨ ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧
      ∃ hns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j))
        (pointY q (ζ ^ i * t ^ j)),
        R = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) hns :=
  TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero_aux hyps hq0 hq hp hp5 hζ ht R hR

end S_TateCurve_eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero
end P2MW
export P2MW.S_TateCurve_eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero (solution)
