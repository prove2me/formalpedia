-- Prove2me | solution 1 for WeierstrassCurve.nonsingular_residue_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3723db08-4c79-57ce-8976-b041888f4306

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace M4cP2
namespace G2

theorem baseChange_map_intCast_eq_map {K : Type*} [CommRing K] [Algebra ℚ K]
    (W : WeierstrassCurve ℤ) : (W.map (Int.castRingHom ℚ))⁄K = W.map (Int.castRingHom K) := by
  show (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) = _
  rw [WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext_int _ _

theorem equation_map_intCast_iff {K : Type*} [CommRing K] (W : WeierstrassCurve ℤ) (x y : K) :
    (W.map (Int.castRingHom K)).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : K) * x * y + (W.a₃ : K) * y
        = x ^ 3 + (W.a₂ : K) * x ^ 2 + (W.a₄ : K) * x + (W.a₆ : K) := by
  rw [Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast]

theorem nonsingular_residue_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation x y)
    (hx : x ∈ A) (hy : y ∈ A) :
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
      (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by
  have hΔ : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 :=
    WeierstrassCurve.map_residueField_discr_ne_zero_of_isGoodPrimeFor W hℓ hgood A hA
  refine (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_

  have hK : y ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x * y + (W.a₃ : AlgebraicClosure ℚ) * y
      = x ^ 3 + (W.a₂ : AlgebraicClosure ℚ) * x ^ 2 + (W.a₄ : AlgebraicClosure ℚ) * x
        + (W.a₆ : AlgebraicClosure ℚ) := by
    rw [baseChange_map_intCast_eq_map W] at h
    exact (equation_map_intCast_iff W x y).mp h

  have hA' : (⟨y, hy⟩ : A) ^ 2 + (W.a₁ : A) * ⟨x, hx⟩ * ⟨y, hy⟩ + (W.a₃ : A) * ⟨y, hy⟩
      = (⟨x, hx⟩ : A) ^ 3 + (W.a₂ : A) * ⟨x, hx⟩ ^ 2 + (W.a₄ : A) * ⟨x, hx⟩ + (W.a₆ : A) := by
    apply Subtype.ext
    push_cast
    exact hK

  have hk := congrArg (IsLocalRing.residue A) hA'
  simp only [map_add, map_mul, map_pow, map_intCast] at hk
  exact (equation_map_intCast_iff W _ _).mpr hk

end M4cP2.G2

theorem solution (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation x y) (hx : x ∈ A) (hy : y ∈ A) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) :=
  M4cP2.G2.nonsingular_residue_of_isGoodPrimeFor W hℓ hgood A hA h hx hy

end S_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor (solution)
