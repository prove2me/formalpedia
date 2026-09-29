-- Prove2me | solution 1 for WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8f45ac4e-31dc-5db4-ab7d-5079a10e8abb

import Mathlib
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (k : Type*) [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := by
  classical

  let K := AlgebraicClosure k
  have hnK : (n : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k K) n]
    exact (map_ne_zero _).mpr hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcard : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hnK
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)

  let φ : (W.toAffine⁄k).Point →+ (W.toAffine⁄K).Point := Point.baseChange k K
  have hφ : Function.Injective φ := Point.map_injective _
  have hmem : ∀ P : Submodule.torsionBy ℤ W.toAffine.Point n, φ P.1 ∈ Submodule.torsionBy ℤ (W⁄K).Point n := by
    intro P
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    show (n : ℤ) • φ P.1 = 0
    rw [← map_zsmul φ]
    exact (congrArg φ hP).trans (map_zero φ)
  refine Finite.of_injective (fun P => (⟨φ P.1, hmem P⟩ : Submodule.torsionBy ℤ (W⁄K).Point n)) ?_
  intro P Q h
  exact Subtype.ext (hφ (congrArg Subtype.val h))

end S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero (solution)
