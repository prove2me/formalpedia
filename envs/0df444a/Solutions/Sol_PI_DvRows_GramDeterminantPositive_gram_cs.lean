-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.gram_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:40.778228+00:00
-- url     : https://prove2.me/submissions/7dba96be-a207-4a56-a2cf-487deb11ebbe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_psd_det_real
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_pd_det_real
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_det_one_add_psd
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_mulVec_injective_of_ker
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution {k : Type*} [Fintype k] [DecidableEq k] (P Q : Matrix m k ℂ) :
    ‖(Pᴴ * Q).det‖ ^ 2 ≤ (Pᴴ * P).det.re * (Qᴴ * Q).det.re := by
  have hP := posSemidef_conjTranspose_mul_self P
  have hQ := posSemidef_conjTranspose_mul_self Q
  obtain ⟨_, hP0⟩ := psd_det_real hP
  obtain ⟨_, hQ0⟩ := psd_det_real hQ
  by_cases hB : (Pᴴ * Q).det = 0
  · rw [hB, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hP0 hQ0
  have hPinj : Function.Injective P.mulVec := mulVec_injective_of_ker fun v hv => by
    by_contra hne
    apply hB
    have h1 : (Pᴴ * Q)ᴴ *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec, hv, mulVec_zero]
    have h0 : (Pᴴ * Q)ᴴ.det = 0 := (exists_mulVec_eq_zero_iff).1 ⟨v, hne, h1⟩
    rwa [det_conjTranspose, star_eq_zero] at h0
  set A := Pᴴ * P with hAdef
  set B := Pᴴ * Q with hBdef
  set D := Qᴴ * Q with hDdef
  have hApd : A.PosDef := PosDef.conjTranspose_mul_self P hPinj
  obtain ⟨hAr, hA0⟩ := pd_det_real hApd
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 (by
    intro h0; rw [h0] at hA0; simp at hA0)
  have hBinj : Function.Injective B.mulVec :=
    (mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB))
  set X := A⁻¹ * B with hXdef
  have hAX : A * X = B := by
    rw [hXdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
  set R := Q - P * X with hRdef
  have hRR : Rᴴ * R = D - Bᴴ * X := by
    have e1 : Qᴴ * (P * X) = Bᴴ * X := by
      rw [hBdef, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    have e2 : Xᴴ * Pᴴ * Q = Xᴴ * B := by rw [hBdef, Matrix.mul_assoc]
    have e3 : Xᴴ * Pᴴ * (P * X) = Xᴴ * B := by
      rw [← hAX, hAdef, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hRdef, conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      e1, e2, e3, hDdef]
    abel
  set C := Bᴴ * X with hCdef
  have hCpd : C.PosDef := by
    have := (hApd.inv).conjTranspose_mul_mul_same hBinj
    rwa [Matrix.mul_assoc] at this
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 (hCpd.det_pos.ne')
  have hD : D = C * (1 + (C⁻¹ * Rᴴ) * R) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
      Matrix.one_mul, hRR]
    abel
  have hN : (R * (C⁻¹ * Rᴴ)).PosSemidef := by
    have := hCpd.inv.posSemidef.mul_mul_conjTranspose_same R
    rwa [Matrix.mul_assoc] at this
  obtain ⟨t, ht1, ht⟩ := det_one_add_psd hN
  set a := A.det.re with ha
  have hbb : star B.det * B.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hdetC : C.det = star B.det * B.det / (a : ℂ) := by
    rw [hCdef, hXdef, det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv', hAr]
    ring
  have hdetD : D.det = ((‖B.det‖ ^ 2 / a * t : ℝ) : ℂ) := by
    rw [hD, det_mul, det_one_add_mul_comm, ht, hdetC, hbb]
    push_cast; ring
  rw [hdetD, Complex.ofReal_re]
  have hb0 : 0 ≤ ‖B.det‖ ^ 2 := sq_nonneg _
  have : a * (‖B.det‖ ^ 2 / a * t) = ‖B.det‖ ^ 2 * t := by field_simp
  rw [this]
  nlinarith
end PI.DvRows.GramDeterminantPositive
