-- Prove2me | solution 1 for WeierstrassCurve.fifteenIsogenyClassification
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/339068e7-18a3-5f14-a987-87d65b0c71cd

import Theorems.Thm_WeierstrassCurve_exists_hauptmodulThree_of_not_modRepIsIrreducible
import Theorems.Thm_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible
import Theorems.Thm_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fifteenIsogenyClassification
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.FifteenA1.deltaPair_zero ModularCurve.FifteenA1.shortW_a₄ ModularCurve.FifteenA1.shortW_a₁ ModularCurve.FifteenA1.shortW_a₂ ModularCurve.FifteenA1.shortW_a₆ ModularCurve.FifteenA1.shortW_a₃"

set_option autoImplicit false

open WeierstrassCurve

theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h3 : ¬ W.ModRepIsIrreducible 3)
    (h5 : ¬ W.ModRepIsIrreducible 5) :
    (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -25 / 2 ∨ (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -349938025 / 8 ∨
      (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -121945 / 32 ∨ (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = 46969655 / 32768 := by
  have hΔQ : ((W.Δ : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hΔ
  obtain ⟨u, -, hrel3⟩ := W.exists_hauptmodulThree_of_not_modRepIsIrreducible hΔ h3
  obtain ⟨v, -, hrel5⟩ := W.exists_hauptmodulFive_of_not_modRepIsIrreducible hΔ h5
  have hk := ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships hΔQ hrel3 hrel5
  simp only [div_eq_iff hΔQ]
  exact hk

end S_WeierstrassCurve_fifteenIsogenyClassification
end P2MW
export P2MW.S_WeierstrassCurve_fifteenIsogenyClassification (solution)
