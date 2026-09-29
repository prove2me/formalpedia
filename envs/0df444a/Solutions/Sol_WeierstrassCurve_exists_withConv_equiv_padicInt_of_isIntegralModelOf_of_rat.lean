-- Prove2me | solution 1 for WeierstrassCurve.exists_withConv_equiv_padicInt_of_isIntegralModelOf_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a8a20b4e-9f81-5a5e-afff-a745bcd1cb7d

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_withConv_equiv_torsionBy_padicAlgClosure_of_ratAlgClosure
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_withConv_equiv_padicInt_of_isIntegralModelOf_of_rat
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

open scoped NNReal

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem solution
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hfin : Module.Finite ℚ A) (hcocomm : Coalgebra.IsCocomm ℚ A)
    (eA : letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
          WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
        (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  obtain ⟨eAp', heAp'_add, heAp'_act⟩ :=
    WeierstrassCurve.exists_withConv_equiv_torsionBy_padicAlgClosure_of_ratAlgClosure
      E p A hfin hcocomm eA heA_add heA_act
  obtain ⟨ψ, hψ⟩ :=
    WeierstrassCurve.exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf E hW p
  refine ⟨eAp'.trans ψ.toEquiv, fun f g => ?_, fun σ f g hgf => ?_⟩
  · show ψ.toEquiv (eAp' (f * g)) = ψ.toEquiv (eAp' f) + ψ.toEquiv (eAp' g)
    rw [heAp'_add f g]
    exact ψ.map_add _ _
  · show ψ.toEquiv (eAp' g) = σ • ψ.toEquiv (eAp' f)
    rw [heAp'_act σ f g hgf]
    exact hψ σ _

end S_WeierstrassCurve_exists_withConv_equiv_padicInt_of_isIntegralModelOf_of_rat
end P2MW
export P2MW.S_WeierstrassCurve_exists_withConv_equiv_padicInt_of_isIntegralModelOf_of_rat (solution)
