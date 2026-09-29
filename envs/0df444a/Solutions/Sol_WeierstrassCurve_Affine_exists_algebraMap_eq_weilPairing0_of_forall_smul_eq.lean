-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f39e9e1d-98a4-57b1-9e40-8b07bd43d5ec

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_galois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_of_forall_smul_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution
    {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] [IsGalois F K]
    (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0)
    (hS' : ∀ σ : K ≃ₐ[F] K, σ • S = S) (hT' : ∀ σ : K ≃ₐ[F] K, σ • T = T) :
    ∃ c : F, algebraMap F K c = ((weilPairing0 W K n S T : Kˣ) : K) := by
  have hfix : ((weilPairing0 W K n S T : Kˣ) : K) ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    have h := WeierstrassCurve.Affine.weilPairing0_galois W hn σ S T hS hT
    rw [hS', hT'] at h
    exact h.symm
  rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hfix
  obtain ⟨c, hc⟩ := hfix
  exact ⟨c, hc⟩

end S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_of_forall_smul_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_of_forall_smul_eq (solution)
