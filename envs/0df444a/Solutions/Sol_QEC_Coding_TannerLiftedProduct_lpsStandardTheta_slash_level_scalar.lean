-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_level_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:28:53.526234+00:00
-- url     : https://prove2.me/submissions/ca530843-4be6-48ab-b4b8-a6dca81563c6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_pos_c
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_scalar
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
        lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat^3) *
      lpsStandardTheta q z := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hcc : (c:ℂ)=(γ 1 0:ℂ) := by exact_mod_cast hci
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h4 : 4 ∣ c := Nat.dvd_trans (show 4 ∣ 16*q^2 from ⟨4*q^2,by ring_nf⟩) hlevel
  obtain ⟨k1,hk1⟩ := h4
  obtain ⟨k8,hk8⟩ := hlevel
  have hk1p : 0 < k1 := by
    by_contra he
    have hz : k1=0 := by omega
    simp [hz] at hk1
    omega
  have hk8p : 0 < k8 := by
    by_contra he
    have hz : k8=0 := by omega
    simp [hz] at hk8
    omega
  have h1 := lpsThetaGaussSum_scalar c 1 k1 (by decide) hk1p
    (by simpa using hk1) (γ 0 0) (γ 0 1) (γ 1 1) hdet z z.im_pos
  have h8 := lpsThetaGaussSum_scalar c (4*q^2) k8 (by positivity) hk8p
    (by dsimp [c];rw [hk8];ring_nf) (γ 0 0) (γ 0 1) (γ 1 1) hdet z z.im_pos
  norm_num only [Nat.cast_one,Int.cast_one,mul_one,one_mul] at h1
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] at h8
  rw [show (2:ℂ)*(4*(q:ℂ)^2)=8*(q:ℂ)^2 by ring_nf] at h8
  have ht : lpsStandardTheta q z = jacobiTheta (2*(z:ℂ))*jacobiTheta (8*(q:ℂ)^2*(z:ℂ))^3 := by
    unfold lpsStandardTheta lpsAnalyticThetaProduct
    congr 2
    push_cast
    ring_nf
  rw [lpsStandardTheta_slash_pos_c q hq γ hc z,← hcc]
  change -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
      lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
      lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 = _
  rw [h1,h8,ht]
  dsimp only [c]
  ring
end QEC.Coding.TannerLiftedProduct
