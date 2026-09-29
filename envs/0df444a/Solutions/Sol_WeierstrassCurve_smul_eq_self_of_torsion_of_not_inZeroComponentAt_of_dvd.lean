-- Prove2me | solution 1 for WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b1861a7b-3154-5453-ae6b-eb468012cc30

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_slope_mem_of_shallow
import Theorems.Thm_WeierstrassCurve_valuation_slope_sub_slope_neg_of_shallow
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_pow_of_dvd
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace S02GLUE

theorem pow_left_inj₀' {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀} {n : ℕ} (hn : n ≠ 0)
    (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hab zero_le' hn))
  · exact hab
  · exact absurd h (ne_of_gt (pow_lt_pow_left₀ hab zero_le' hn))

end S02GLUE

open S02GLUE in
theorem solution
    (W : WeierstrassCurve ℤ) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hv : ℓ ∣ padicValInt q W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hM : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, ℓ • P = 0 →
        W.InZeroComponentAt A P → σ • P = P)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : ℓ • P = 0)
    (hnot : ¬ W.InZeroComponentAt A P) :
    σ • P = P := by

  have _ := hM

  obtain _ | @⟨x, y, h⟩ := P
  · exact (hnot (Or.inl rfl)).elim

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, hfix⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hq hΔ hqΔ hqc₄ A hA
  obtain ⟨hσx₀, hσy₀⟩ := hfix σ hσ

  have hX : A.valuation (x - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode hbad h).mp hnot
  have hDisc := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode hbad
  have hAq : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hA

  have hΔpow := ValuationSubring.valuation_intCast_eq_pow_pow_of_dvd A hq hAq hΔ hv
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    have hq2 : q ≠ 2 := fun h2 => hℓq h2.symm
    obtain ⟨hlev2, -⟩ := WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt W hq hq2 A hA
      hx₀ hy₀ hFy hFx hnode hbad h hP hX
    have hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ (padicValInt q W.Δ / 2) := by
      apply pow_left_inj₀' two_ne_zero
      rw [hlev2, ← hDisc, hΔpow]
    exact WeierstrassCurve.Affine.Point.smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level W hq hq2 A hA
      hx₀ hy₀ hFy hFx hnode hbad hσ hσx₀ h hP hX _ hlev
  ·
    obtain ⟨hshΔ, j, hj1, hj2, hpow⟩ :=
      WeierstrassCurve.valuation_pow_eq_of_torsion_of_not_inZeroComponentAt W hq hΔ hqΔ hqc₄ A hA
        hx₀ hy₀ hFy hFx hnode hbad hℓ hℓ2 hℓq h hP hX

    have hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ (padicValInt q W.Δ / ℓ * j) := by
      apply pow_left_inj₀' hℓ.ne_zero
      rw [hpow, hΔpow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm ℓ j, mul_assoc]

    have hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        < A.valuation (x - x₀) ^ 2 := by rw [← hDisc]; exact hshΔ
    obtain ⟨ht, -, -⟩ := WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h hX hsh
    have hneg := WeierstrassCurve.valuation_slope_sub_slope_neg_of_shallow W A hx₀ hy₀ hFy hFx hnode h hX hsh
    have hX0 : x - x₀ ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero, zero_pow two_ne_zero] at hsh
      exact absurd hsh (not_lt.mpr zero_le')

    have ca₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.a₁ = (W.a₁ : AlgebraicClosure ℚ) := by
      simp
    have ca₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.a₃ = (W.a₃ : AlgebraicClosure ℚ) := by
      simp

    have hqℓ : ¬ q ∣ ℓ := fun hd => hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp hd).symm

    refine WeierstrassCurve.Affine.Point.smul_eq_self_of_mem_inertiaSubgroupIn_of_level
      (W.map (Int.castRingHom ℚ)) A hq hσ x₀ y₀ ((y - y₀) / (x - x₀))
      (-((y - y₀) / (x - x₀)) - (W.a₁ : AlgebraicClosure ℚ)) hσx₀ hσy₀ ht ?_ ?_ ?_ h hP _ hlev ?_ ?_
    ·
      have key : (y - y₀) / (x - x₀) - (-((y - y₀) / (x - x₀)) - (W.a₁ : AlgebraicClosure ℚ))
          = (y - y₀) / (x - x₀)
            - (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.negY x y - y₀) / (x - x₀) := by
        rw [WeierstrassCurve.Affine.negY, ca₁, ca₃]
        field_simp
        linear_combination -hFy
      rw [key]; exact hneg
    ·
      rw [ca₁, show (y - y₀) / (x - x₀) + (-((y - y₀) / (x - x₀)) - (W.a₁ : AlgebraicClosure ℚ))
        + (W.a₁ : AlgebraicClosure ℚ) = 0 by ring, Valuation.map_zero]
      exact zero_lt_one
    ·
      rw [ca₁, ca₃]; exact hFy
    ·
      rw [div_mul_cancel₀ _ hX0, sub_self, Valuation.map_zero]
      exact lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr hX0))
    ·
      intro x' y' h' hP' hlev' hne hne'
      have hX' : A.valuation (x' - x₀) < 1 := by rw [hlev']; exact hX
      have hsh' : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          < A.valuation (x' - x₀) ^ 2 := by rw [hlev']; exact hsh
      obtain ⟨ht', -, -⟩ := WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h' hX' hsh'
      have hle : A.valuation ((y' - y₀) / (x' - x₀) - (y - y₀) / (x - x₀)) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (sub_mem ht' ht)
      rcases hle.lt_or_eq with hsame | hopp
      ·
        obtain ⟨-, hsharp⟩ := WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq W A hx₀ hy₀ hFy hFx
          hnode hbad h' h hX' hX hlev' hsh' hsame
        have hD0 : Point.some x' y' h' - Point.some x y h ≠ 0 := sub_ne_zero.mpr hne
        have hDtor : ℓ • (Point.some x' y' h' - Point.some x y h) = 0 := by rw [nsmul_sub, hP', hP, sub_zero]
        rcases WeierstrassCurve.torsion_integral_of_not_dvd W hq A hA hqℓ _ hDtor with hD | ⟨x₃, y₃, h₃, hD, hx₃, -⟩
        · exact absurd hD hD0
        · rw [← hlev']; exact hsharp h₃ hD hx₃
      ·
        obtain ⟨-, hsharp⟩ := WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne W A hx₀ hy₀ hFy hFx
          hnode hbad h' h hX' hX hlev' hsh' hopp
        have hD0 : Point.some x' y' h' + Point.some x y h ≠ 0 := fun h0 => hne' (add_eq_zero_iff_eq_neg.mp h0)
        have hDtor : ℓ • (Point.some x' y' h' + Point.some x y h) = 0 := by rw [nsmul_add, hP', hP, add_zero]
        rcases WeierstrassCurve.torsion_integral_of_not_dvd W hq A hA hqℓ _ hDtor with hD | ⟨x₃, y₃, h₃, hD, hx₃, -⟩
        · exact absurd hD hD0
        · rw [← hlev']; exact hsharp h₃ hD hx₃

end S_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
end P2MW
export P2MW.S_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd (solution)
