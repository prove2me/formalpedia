-- Prove2me | solution 1 for WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/44ced18d-81d5-53bc-96d4-ac1b59eacf88

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic
import Theorems.Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p =>
        (⟨WeierstrassCurve.Affine.Point.map ι (P : (E⁄(AlgebraicClosure ℚ)).Point), by
          have hP := (Submodule.mem_torsionBy_iff _ _).mp P.property
          rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP]
          exact _root_.map_zero _⟩ :
        Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ_[p])).Point p)) := by
  by_cases hE : E.IsElliptic
  · exact WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic E p ι
  · exact WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic E hE p ι

end S_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure
end P2MW
export P2MW.S_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure (solution)
