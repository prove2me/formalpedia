-- Prove2me | solution 1 for WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fe63901d-86a1-59c5-8c8b-5542a900a852

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_EllipticCurve_FrobeniusEndo
import Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField
import Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_one_one
import Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_line
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_det_frobenius_tateModule_eq_card
import Theorems.Thm_LinearMap_trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_trace_frobenius_tateModule_eq_card_add_one_sub
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace TraceFrobeniusTateModuleAux

theorem intCast_padicInt_smul_apply {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (c : ℤ) (x : TateModule p M) (n : ℕ) :
    (((c : ℤ_[p]) • x : TateModule p M) : ℕ → M) n = c • (x : ℕ → M) n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · rw [Int.cast_natCast, TateModule.natCast_padicInt_smul_apply]
  · rw [Int.cast_neg, Int.cast_natCast, neg_smul, TateModule.coe_neg, Pi.neg_apply,
      TateModule.natCast_padicInt_smul_apply, neg_smul]

theorem rep_sq_sub_smul_add_eq_zero {F : Type*} [Field F] {k : Type} [Field k] [DecidableEq k]
    [Algebra F k] (W : WeierstrassCurve F) (σ : k ≃ₐ[F] k) (ℓ : ℕ) [Fact ℓ.Prime] (a : ℤ) (q : ℕ)
    (hchar : FrobeniusEndo.FrobCharEqOnPoints W σ a q) :
    TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ * TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ
        - (a : ℤ_[ℓ]) • TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ
        + (q : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] (TateModule ℓ (W⁄k).Point)) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  show ((TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ (TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ x)
      - ((a : ℤ) : ℤ_[ℓ]) • TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ x
      + ((q : ℕ) : ℤ_[ℓ]) • x : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
    = ((0 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
  rw [TateModule.coe_add, TateModule.coe_sub, Pi.add_apply, Pi.sub_apply,
    intCast_padicInt_smul_apply, TateModule.natCast_padicInt_smul_apply, TateModule.rep_apply,
    TateModule.rep_apply, TateModule.coe_zero, Pi.zero_apply]
  exact hchar _

theorem baseChange_self {F : Type*} [Field F] (W : WeierstrassCurve F) : (W⁄F) = W := by
  show W.map (algebraMap F F) = W
  rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem frobCharEqOnPoints {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k]
    [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k)
    (hσ : ∀ x : k, σ x = x ^ Fintype.card F) :
    FrobeniusEndo.FrobCharEqOnPoints W σ
      ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) (Fintype.card F) := by
  haveI : (W⁄k).IsElliptic := by
    show (W.map (algebraMap F k)).IsElliptic
    infer_instance

  have hone : ((FrobeniusEndo.kerDeg (FrobeniusEndo.frobEnd W σ) 1 1 : ℕ) : ℤ)
      = (Nat.card W.toAffine.Point : ℤ) := by
    rw [FrobeniusEndo.kerDeg_frobEnd_one_one W σ hσ, baseChange_self]

  have hline := fun (m : ℕ) (hm : 1 ≤ m) (hmk : (m : k) ≠ 0) =>
    FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField (R := F) W σ hσ m hm hmk
  refine FrobeniusEndo.frobCharEqOnPoints_of_line (R := F) W σ hσ _ ?_ ?_ ?_
  · intro m hm hmk
    rw [(hline m hm hmk).2, hone]
  · intro m hm hmk
    exact (hline m hm hmk).1.ne'
  · intro r _ hrk
    exact WeierstrassCurve.card_torsion_of_isAlgClosed W hrk

end TraceFrobeniusTateModuleAux

open TraceFrobeniusTateModuleAux in

theorem solution {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) : LinearMap.trace ℤ_[ℓ] (TateModule ℓ (W⁄k).Point) (TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ) = (((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : ℤ_[ℓ]) := by
  classical

  have hℓk : (ℓ : k) ≠ 0 := fun h =>
    hℓ ((algebraMap F k).injective (by rw [map_natCast, _root_.map_zero, h]))
  have hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 2 := fun n =>
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓk)

  haveI : Module.Free ℤ_[ℓ] (TateModule ℓ (W⁄k).Point) := TateModule.free hcard
  haveI : Module.Finite ℤ_[ℓ] (TateModule ℓ (W⁄k).Point) := TateModule.finite hcard
  have hrank : Module.finrank ℤ_[ℓ] (TateModule ℓ (W⁄k).Point) = 2 :=
    TateModule.finrank_eq_two hcard

  have hrel := rep_sq_sub_smul_add_eq_zero W σ ℓ _ _ (frobCharEqOnPoints W σ hσ)

  have hdet : LinearMap.det (TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ)
      = ((Fintype.card F : ℕ) : ℤ_[ℓ]) :=
    WeierstrassCurve.det_frobenius_tateModule_eq_card W σ hσ ℓ hℓ
  have hq : ((Fintype.card F : ℕ) : ℤ_[ℓ]) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero

  exact LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq hrank _ _ _ hrel hdet hq

end S_WeierstrassCurve_trace_frobenius_tateModule_eq_card_add_one_sub
end P2MW
export P2MW.S_WeierstrassCurve_trace_frobenius_tateModule_eq_card_add_one_sub (solution)
