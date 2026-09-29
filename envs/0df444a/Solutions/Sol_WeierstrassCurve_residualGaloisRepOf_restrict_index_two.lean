-- Prove2me | solution 1 for WeierstrassCurve.residualGaloisRepOf_restrict_index_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7b64c8e4-b6fb-5d0b-a4d1-bc5b2537be63

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
import Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
import Theorems.Thm_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd
import Theorems.Thm_WeierstrassCurve_galoisRep_inertia_unipotent_of_isSemistableModel
import Theorems.Thm_WeierstrassCurve_galoisRep_ordinaryLineAt
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_galoisRep_supersingularShapeAt
import Theorems.Thm_WeierstrassCurve_card_range_galoisRep_three_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_residualGaloisRepOf_restrict_index_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hirr : WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (K : Type) [Field K] [Algebra (ZMod p) K]
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hH : H.index = 2)
    (ℓ : Submodule K (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChange K).V)
    (hℓ : ∀ σ ∈ H, ∀ x ∈ ℓ,
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChange K).ρ σ x ∈ ℓ) :
    ℓ = ⊥ ∨ ℓ = ⊤ := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact isUnit_iff_ne_zero.mpr (by simpa using hΔ)⟩
  have hirr' : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).IsIrreducible :=
    (WeierstrassCurve.residualGaloisRepOf_isIrreducible_iff _ p hcard hker).mpr hirr
  have hodd' : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).IsOdd :=
    WeierstrassCurve.residualGaloisRepOf_isOdd _ p hcard hker
  refine ResidualGaloisRep.restrict_index_two_of_isIrreducible_of_isOdd hp2 _ hirr' hodd'
    AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le
    ?_ ?_ ?_ ?_ K H hH ℓ hℓ
  · intro q hq hqp A hA σ hσ
    exact W.galoisRep_inertia_unipotent_of_isSemistableModel p hΔ hW hcard hker hq hqp A hA σ hσ
  · intro A hA a
    exact W.det_galoisRep_surjOn_inertia p hΔ A hA a
  · by_cases hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i
    · left
      intro A hA
      exact W.galoisRep_ordinaryLineAt p hp2 hΔ hW hord A hA
    · right
      push Not at hord
      obtain ⟨hpΔ, hss⟩ := hord
      intro A hA
      exact W.galoisRep_supersingularShapeAt p hp2 hpΔ (fun i h1 h2 => hss i h1 h2) hcard A hA
  · intro hp3 hunr hle2
    subst hp3
    exact W.card_range_galoisRep_three_le_two hΔ hcard hunr hle2

#print axioms solution

end S_WeierstrassCurve_residualGaloisRepOf_restrict_index_two
end P2MW
export P2MW.S_WeierstrassCurve_residualGaloisRepOf_restrict_index_two (solution)
