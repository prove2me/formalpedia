-- Prove2me | solution 1 for WeierstrassCurve.card_p_torsion_le_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fbef4b6e-81fa-565d-a49b-c174d8ba6a82

import Mathlib
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) ≤ p ^ 2 := by
  classical
  let K := AlgebraicClosure F
  have hpK : (p : K) ≠ 0 := by
    intro h
    apply hpF
    have h1 : algebraMap F K (p : F) = algebraMap F K 0 := by rw [map_natCast, map_zero, h]
    exact (algebraMap F K).injective h1
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) W hpK
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) := Finite.of_equiv _ e.toEquiv
  have hcardK : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) = p ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]
    ring

  let f : W.toAffine.Point →+ (W⁄K).toAffine.Point := Point.map (W' := W) (Algebra.ofId F K)
  have hmem : ∀ P : Submodule.torsionBy ℤ W.toAffine.Point p,
      f P ∈ Submodule.torsionBy ℤ (W⁄K).toAffine.Point p := by
    intro P
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul f, hP, map_zero]
  let ι : Submodule.torsionBy ℤ W.toAffine.Point p → Submodule.torsionBy ℤ (W⁄K).toAffine.Point p :=
    fun P => ⟨f P, hmem P⟩
  have hι : Function.Injective ι := by
    intro P Q h
    apply Subtype.ext
    exact Point.map_injective (Algebra.ofId F K) (congrArg Subtype.val h)
  calc Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p)
      ≤ Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) := Nat.card_le_card_of_injective ι hι
    _ = p ^ 2 := hcardK

end S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero (solution)
