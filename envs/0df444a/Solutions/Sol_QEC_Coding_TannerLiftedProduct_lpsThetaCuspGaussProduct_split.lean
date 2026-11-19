-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:45:41.623472+00:00
-- url     : https://prove2.me/submissions/b8666a30-e6f1-4a1f-9b42-932f23c71fc9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_coprime_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_odd_unit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t v L : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (hL : 0<L) (hcL : L.Coprime (2*q)) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^t*q^v*L))) :
    lpsThetaCuspGaussProduct q a (2^t*q^v*L)=
      (L:ℂ)^2*lpsThetaCuspGaussProduct q (a*((q^v*L:ℕ):ℤ)) (2^t)*
        lpsThetaCuspGaussProduct q (a*((2^t*L:ℕ):ℤ)) (q^v) := by
  have hqpos : 0<q := (Fact.out : q.Prime).pos
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero (2^t*q^v*L) := ⟨by positivity⟩
  let : NeZero (q^v*L) := ⟨by positivity⟩
  have hL2 : L.Coprime 2 := hcL.coprime_dvd_right (dvd_mul_right _ _)
  have hLq : L.Coprime q := hcL.coprime_dvd_right (dvd_mul_left _ _)
  have h2q := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left
  have h2rest : (2^t).Coprime (q^v*L) :=
    ((h2q.pow_right v).mul_right hL2.symm).pow_left t
  have hqL : (q^v).Coprime L := hLq.symm.pow_left v
  have hcofactor : (2^t*q^v).Coprime L := (hL2.symm.pow_left t).mul_left hqL
  have haL := lpsZMod_unit_descend (2^t*q^v*L) L (dvd_mul_left _ _) a ha
  have hau : IsUnit (((a*((2^t*q^v:ℕ):ℤ)):ℤ):ZMod L) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using
      haL.mul ((ZMod.isUnit_iff_coprime (2^t*q^v) L).mpr hcofactor)
  have h2qu : IsUnit ((2*q:ℕ):ZMod L) := (ZMod.isUnit_iff_coprime (2*q) L).mpr hcL.symm
  have hodd : Odd L := hL2.odd_of_right
  rw [show 2^t*q^v*L=2^t*(q^v*L) by ring,
    lpsThetaCuspGaussProduct_coprime_mul q (2^t) (q^v*L) h2rest a,
    lpsThetaCuspGaussProduct_coprime_mul q (q^v) L hqL (a*((2^t:ℕ):ℤ))]
  have heL : (a*((2^t:ℕ):ℤ))*((q^v:ℕ):ℤ)=a*((2^t*q^v:ℕ):ℤ) := by push_cast;ring
  have heq : (a*((2^t:ℕ):ℤ))*(L:ℤ)=a*((2^t*L:ℕ):ℤ) := by push_cast;ring
  rw [heL,heq,lpsThetaCuspGaussProduct_odd_unit q L hodd _ hau h2qu]
  ring
end QEC.Coding.TannerLiftedProduct
