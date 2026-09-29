-- Prove2me | solution 1 for WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/655391f3-526e-5460-b27a-bb56a024ec50

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_slope_mem_of_shallow
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace NonbotPort

theorem exists_eq_some {F : Type*} [Field F] {W' : WeierstrassCurve F} :
    ∀ P : W'.toAffine.Point, P ≠ 0 → ∃ (x y : F) (h : W'.toAffine.Nonsingular x y), P = .some x y h := by
  rintro (_ | ⟨x, y, h⟩) hP
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl⟩

theorem pow_left_inj₀' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} {n : ℕ} (hn : n ≠ 0)
    (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (pow_lt_pow_left₀ hab zero_le' hn).ne
  · exact hab
  · exact absurd h (pow_lt_pow_left₀ hab zero_le' hn).ne'

noncomputable abbrev E (W : WeierstrassCurve ℤ) : WeierstrassCurve (AlgebraicClosure ℚ) :=
  ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) : WeierstrassCurve (AlgebraicClosure ℚ))

theorem isElliptic_map (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) : (W.map (Int.castRingHom ℚ)).IsElliptic :=
  ⟨by rw [WeierstrassCurve.map_Δ, eq_intCast]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hΔ)⟩

section centre

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
  {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
  (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
  (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
  (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
  (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
    - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)

include hx₀ hy₀ hFy hFx hnode hbad in

theorem eq_or_eq_neg_of_level_eq {ℓ : ℕ}
    (hzero : ∀ Q : (E W).toAffine.Point, ℓ • Q = 0 → W.InZeroComponentAt A Q → Q = 0)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (E W).toAffine.Nonsingular x₁ y₁) (h₂ : (E W).toAffine.Nonsingular x₂ y₂)
    (htor₁ : ℓ • (Point.some x₁ y₁ h₁) = 0) (htor₂ : ℓ • (Point.some x₂ y₂ h₂) = 0)
    (hX₁ : A.valuation (x₁ - x₀) < 1) (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hlev : A.valuation (x₁ - x₀) = A.valuation (x₂ - x₀))
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₁ - x₀) ^ 2) :
    Point.some x₂ y₂ h₂ = Point.some x₁ y₁ h₁ ∨ Point.some x₂ y₂ h₂ = - Point.some x₁ y₁ h₁ := by

  have ht₁ := (WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h₁ hX₁ hsh).1
  have hsh₂ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₂ - x₀) ^ 2 := hlev ▸ hsh
  have ht₂ := (WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h₂ hX₂ hsh₂).1
  have hle : A.valuation ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (sub_mem ht₁ ht₂)
  rcases hle.lt_or_eq with hbr | hbr
  ·
    have hE0 := (WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq W A hx₀ hy₀ hFy hFx
      hnode hbad h₁ h₂ hX₁ hX₂ hlev hsh hbr).1
    have htor : ℓ • (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) = 0 := by
      rw [nsmul_sub, htor₁, htor₂, sub_zero]
    left
    exact (sub_eq_zero.mp (hzero _ htor hE0)).symm
  ·
    have hE0 := (WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne W A hx₀ hy₀ hFy hFx
      hnode hbad h₁ h₂ hX₁ hX₂ hlev hsh hbr).1
    have htor : ℓ • (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) = 0 := by
      rw [nsmul_add, htor₁, htor₂, add_zero]
    right
    exact eq_neg_of_add_eq_zero_right (hzero _ htor hE0)

end centre

end NonbotPort

open NonbotPort in
theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ, P ≠ 0 ∧ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
  by_contra hcon
  push Not at hcon

  have hzero : ∀ Q : (E W).toAffine.Point, ℓ • Q = 0 → W.InZeroComponentAt A Q → Q = 0 := by
    intro Q hQ hQ0
    by_contra hne
    have hmem : Q ∈ Submodule.torsionBy ℤ (E W).toAffine.Point ℓ := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQ
    exact hcon ⟨Q, hmem⟩ (fun h0 => hne (congrArg Subtype.val h0)) hQ0

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hq hΔ hqΔ hqc₄ A hA
  have hDisc := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode hbad

  have hnode_red : ∀ P : Submodule.torsionBy ℤ (E W).toAffine.Point ℓ, P ≠ 0 →
      ∃ (x y : AlgebraicClosure ℚ) (h : (E W).toAffine.Nonsingular x y),
        (P : (E W).toAffine.Point) = .some x y h ∧ ℓ • (Point.some x y h) = 0 ∧
          A.valuation (x - x₀) < 1 := by
    intro P hP
    have hP' : (P : (E W).toAffine.Point) ≠ 0 := fun h0 => hP (Subtype.ext h0)
    obtain ⟨x, y, h, hPeq⟩ := exists_eq_some _ hP'
    have htor : ℓ • (Point.some x y h) = 0 := by
      have := (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mp P.2
      rw [natCast_zsmul] at this
      rw [← hPeq]; exact this
    have hnot : ¬ W.InZeroComponentAt A (.some x y h) := hPeq ▸ hcon P hP
    exact ⟨x, y, h, hPeq, htor, (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A
      hx₀ hy₀ hFy hFx hnode hbad h).mp hnot⟩

  haveI := isElliptic_map W hΔ
  have hℓ0 : ((ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hcard : Nat.card (Submodule.torsionBy ℤ (E W).toAffine.Point ℓ) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (W.map (Int.castRingHom ℚ)) hℓ0
  haveI : Finite (Submodule.torsionBy ℤ (E W).toAffine.Point ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hℓ.ne_zero)
  letI : Fintype (Submodule.torsionBy ℤ (E W).toAffine.Point ℓ) := Fintype.ofFinite _
  classical
  set s : Finset (Submodule.torsionBy ℤ (E W).toAffine.Point ℓ) := Finset.univ.erase 0 with hs
  have hscard : s.card = ℓ ^ 2 - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      hcard]
  have hmem_s : ∀ {P}, P ∈ s ↔ P ≠ 0 := by
    intro P; simp [hs]
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  ·
    have hq2 : q ≠ 2 := fun h => hℓq h.symm

    have h1 : 1 < s.card := by rw [hscard]; norm_num
    obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := Finset.one_lt_card.mp h1

    obtain ⟨x₁, y₁, h₁, hP₁eq, htor₁, hX₁⟩ := hnode_red P₁ (hmem_s.mp hP₁)
    obtain ⟨x₂, y₂, h₂, hP₂eq, htor₂, hX₂⟩ := hnode_red P₂ (hmem_s.mp hP₂)
    have hanti₁ := (WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt W hq hq2 A hA
      hx₀ hy₀ hFy hFx hnode hbad h₁ htor₁ hX₁).1
    have hanti₂ := (WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt W hq hq2 A hA
      hx₀ hy₀ hFy hFx hnode hbad h₂ htor₂ hX₂).1
    have hsum := WeierstrassCurve.inZeroComponentAt_add_of_antipodal W A hx₀ hy₀ hFy hFx hnode hbad
      h₁ h₂ hX₁ hanti₁.le hX₂ hanti₂.le

    have htor : 2 • (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) = 0 := by
      rw [nsmul_add, htor₁, htor₂, add_zero]
    have hsum0 := hzero _ htor hsum

    apply hne
    apply Subtype.ext
    rw [hP₁eq, hP₂eq]
    have hneg : Point.some x₁ y₁ h₁ = - Point.some x₂ y₂ h₂ := eq_neg_of_add_eq_zero_left hsum0
    have hself : - Point.some x₂ y₂ h₂ = Point.some x₂ y₂ h₂ := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact htor₂
    rw [hneg, hself]
  ·

    have hdata : ∀ P : Submodule.torsionBy ℤ (E W).toAffine.Point ℓ, P ≠ 0 →
        ∃ (x y : AlgebraicClosure ℚ) (h : (E W).toAffine.Nonsingular x y),
          (P : (E W).toAffine.Point) = .some x y h ∧ ℓ • (Point.some x y h) = 0 ∧
            A.valuation (x - x₀) < 1 ∧
            A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2 ∧
            ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧
              A.valuation (x - x₀) ^ ℓ = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ j := by
      intro P hP
      obtain ⟨x, y, h, hPeq, htor, hX⟩ := hnode_red P hP
      obtain ⟨hsh, j, hj1, hj2, hjpow⟩ :=
        WeierstrassCurve.valuation_pow_eq_of_torsion_of_not_inZeroComponentAt W hq hΔ hqΔ hqc₄ A hA
          hx₀ hy₀ hFy hFx hnode hbad hℓ hℓ2 hℓq h htor hX
      exact ⟨x, y, h, hPeq, htor, hX, hDisc ▸ hsh, j, hj1, hj2, hjpow⟩
    choose! fx fy fh hPeq htor hX hsh fj hj1 hj2 hjpow using hdata

    have himage : s.image fj ⊆ Finset.Icc 1 ((ℓ - 1) / 2) := by
      intro j hj
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hj
      have hP0 := hmem_s.mp hP
      have := hj1 P hP0; have := hj2 P hP0
      rw [Finset.mem_Icc]; omega
    have hcard_image : (s.image fj).card ≤ (ℓ - 1) / 2 := by
      refine (Finset.card_le_card himage).trans ?_
      rw [Nat.card_Icc]; omega

    have hfibre : ∀ j ∈ s.image fj, (s.filter fun P => fj P = j).card ≤ 2 := by
      intro j hj
      obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.mp hj
      have hP₁0 := hmem_s.mp hP₁
      suffices hsub : (s.filter fun P => fj P = fj P₁) ⊆ {P₁, -P₁} from
        (Finset.card_le_card hsub).trans Finset.card_le_two
      intro P₂ hP₂
      rw [Finset.mem_filter] at hP₂
      obtain ⟨hP₂s, hjj⟩ := hP₂
      have hP₂0 := hmem_s.mp hP₂s

      have hlev : A.valuation (fx P₁ - x₀) = A.valuation (fx P₂ - x₀) := by
        apply pow_left_inj₀' hℓ.ne_zero
        rw [hjpow P₁ hP₁0, hjpow P₂ hP₂0, hjj]
      have key := eq_or_eq_neg_of_level_eq W A hx₀ hy₀ hFy hFx hnode hbad hzero
        (fh P₁ hP₁0) (fh P₂ hP₂0) (htor P₁ hP₁0) (htor P₂ hP₂0) (hX P₁ hP₁0) (hX P₂ hP₂0) hlev
        (hsh P₁ hP₁0)
      rw [← hPeq P₁ hP₁0, ← hPeq P₂ hP₂0] at key
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases key with k | k
      · exact Or.inl (Subtype.ext k)
      · exact Or.inr (Subtype.ext (by rw [k]; rfl))
    have hbound := Finset.card_le_mul_card_image s 2 hfibre

    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le; omega
    have hsq : 3 * ℓ ≤ ℓ ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right ℓ h3
    have := hcard_image
    omega

end S_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar (solution)
