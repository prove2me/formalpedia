-- Prove2me | solution 1 for WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/adbaefb0-f854-5823-a0a5-f9eaf82f83f0

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve F) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) :
    Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩

  have hpK : (p : K) ≠ 0 := by
    simpa using fun h => hpF (FaithfulSMul.algebraMap_injective F K (by simpa using h))

  have hcard : Nat.card (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed E (n := p) hpK

  set M := Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p
  have hne : Nat.card M ≠ 0 := hcard ▸ pow_ne_zero 2 hp.pos.ne'
  haveI : Finite M := Nat.finite_of_card_ne_zero hne
  haveI : Fintype M := Fintype.ofFinite M
  have hceq : Fintype.card M = p ^ Module.finrank (ZMod p) M := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := M)
    rwa [ZMod.card] at h
  rw [← Nat.card_eq_fintype_card, hcard] at hceq
  exact (Nat.pow_right_injective hp.two_le hceq).symm

end S_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
end P2MW
export P2MW.S_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two (solution)
