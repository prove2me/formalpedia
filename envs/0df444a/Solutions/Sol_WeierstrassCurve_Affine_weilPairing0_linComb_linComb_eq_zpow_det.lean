-- Prove2me | solution 1 for WeierstrassCurve.Affine.weilPairing0_linComb_linComb_eq_zpow_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/76977ecd-7a45-599c-8c8c-83e009299edd

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_left
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_right
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_linComb_linComb_eq_zpow_det
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem solution
    {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0)
    (g : Matrix (Fin 2) (Fin 2) ℤ) :
    weilPairing0 W K n (g 0 0 • S + g 1 0 • T) (g 0 1 • S + g 1 1 • T) =
      weilPairing0 W K n S T ^ g.det := by

  set e : (W⁄K).Point → (W⁄K).Point → Kˣ := fun A B => weilPairing0 W K n A B with he
  have he' : ∀ A B, weilPairing0 W K n A B = e A B := fun _ _ => rfl
  simp only [he']

  have tor_add : ∀ {A B : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • B = 0 → (n : ℤ) • (A + B) = 0 := by
    intro A B hA hB; rw [smul_add, hA, hB, add_zero]
  have tor_zsmul : ∀ (a : ℤ) {A : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • (a • A) = 0 := by
    intro a A hA; rw [smul_comm, hA, smul_zero]
  have tor_zero : (n : ℤ) • (0 : (W⁄K).Point) = 0 := smul_zero _

  have addL : ∀ {A A' B : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • A' = 0 → (n : ℤ) • B = 0 →
      e (A + A') B = e A B * e A' B := fun hA hA' hB => weilPairing0_add_left W hn _ _ _ hA hA' hB
  have addR : ∀ {A B B' : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • B = 0 → (n : ℤ) • B' = 0 →
      e A (B + B') = e A B * e A B' := fun hA hB hB' => weilPairing0_add_right W hn _ _ _ hA hB hB'
  have self1 : ∀ {A : (W⁄K).Point}, (n : ℤ) • A = 0 → e A A = 1 := fun hA => weilPairing0_self W hn _ hA

  have zeroL : ∀ {B : (W⁄K).Point}, (n : ℤ) • B = 0 → e 0 B = 1 := by
    intro B hB
    have h := addL tor_zero tor_zero hB
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have zeroR : ∀ {A : (W⁄K).Point}, (n : ℤ) • A = 0 → e A 0 = 1 := by
    intro A hA
    have h := addR hA tor_zero tor_zero
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm

  have zsmulL : ∀ (a : ℤ) {A B : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • B = 0 → e (a • A) B = e A B ^ a := by
    intro a A B hA hB
    induction a using Int.induction_on with
    | zero => rw [zero_smul, zpow_zero]; exact zeroL hB
    | succ i ih => rw [add_smul, one_smul, addL (tor_zsmul _ hA) hA hB, ih, zpow_add, zpow_one]
    | pred i ih =>
      have h := addL (tor_zsmul ((-(i : ℤ)) - 1) hA) hA hB
      rw [show ((-(i : ℤ)) - 1) • A + A = (-(i : ℤ)) • A by rw [sub_smul, one_smul, sub_add_cancel], ih] at h
      rw [eq_mul_inv_of_mul_eq h.symm, ← zpow_sub_one]
  have zsmulR : ∀ (a : ℤ) {A B : (W⁄K).Point}, (n : ℤ) • A = 0 → (n : ℤ) • B = 0 → e A (a • B) = e A B ^ a := by
    intro a A B hA hB
    induction a using Int.induction_on with
    | zero => rw [zero_smul, zpow_zero]; exact zeroR hA
    | succ i ih => rw [add_smul, one_smul, addR hA (tor_zsmul _ hB) hB, ih, zpow_add, zpow_one]
    | pred i ih =>
      have h := addR hA (tor_zsmul ((-(i : ℤ)) - 1) hB) hB
      rw [show ((-(i : ℤ)) - 1) • B + B = (-(i : ℤ)) • B by rw [sub_smul, one_smul, sub_add_cancel], ih] at h
      rw [eq_mul_inv_of_mul_eq h.symm, ← zpow_sub_one]

  have skew : e T S = (e S T)⁻¹ := by
    have h := self1 (tor_add hS hT)
    rw [addL hS hT (tor_add hS hT), addR hS hS hT, addR hT hS hT, self1 hS, self1 hT, one_mul, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h

  have hS' : ∀ a : ℤ, (n : ℤ) • (a • S) = 0 := fun a => tor_zsmul a hS
  have hT' : ∀ a : ℤ, (n : ℤ) • (a • T) = 0 := fun a => tor_zsmul a hT
  rw [addL (hS' _) (hT' _) (tor_add (hS' _) (hT' _)), addR (hS' _) (hS' _) (hT' _), addR (hT' _) (hS' _) (hT' _),
    zsmulL _ hS (hS' _), zsmulL _ hS (hT' _), zsmulL _ hT (hS' _), zsmulL _ hT (hT' _),
    zsmulR _ hS hS, zsmulR _ hS hT, zsmulR _ hT hS, zsmulR _ hT hT, self1 hS, self1 hT, skew]
  simp only [one_zpow, one_mul, mul_one, inv_zpow', ← zpow_mul, ← zpow_add]
  rw [Matrix.det_fin_two]
  congr 1
  ring

end S_WeierstrassCurve_Affine_weilPairing0_linComb_linComb_eq_zpow_det
end P2MW
export P2MW.S_WeierstrassCurve_Affine_weilPairing0_linComb_linComb_eq_zpow_det (solution)
