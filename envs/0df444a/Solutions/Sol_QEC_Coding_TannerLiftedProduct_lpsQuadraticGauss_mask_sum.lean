-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:33.501566+00:00
-- url     : https://prove2.me/submissions/40a82f1f-8766-4a05-b2d0-b89bbe1056f4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_mask_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_sum_residue_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_scaled_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier (d*m) (a:ZMod (d*m))
      (((m:ℤ)*j.val:ℤ):ZMod (d*m))) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) := by
  classical
  unfold lpsQuadraticFourier
  rw [Finset.sum_comm]
  simp_rw [AddChar.map_add_eq_mul,← Finset.mul_sum]
  have h (r : ZMod (d*m)) :
      (∑ j : Fin d, ZMod.stdAddChar
        ((((m:ℤ)*j.val:ℤ):ZMod (d*m))*r)) =
      if (r.val:ZMod d)=0 then (d:ℂ) else 0 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val r]
    have he := lpsChar_mask_sum d m r.val
    convert he using 1 <;> push_cast <;> rfl
  simp_rw [h]
  rw [lpsZMod_sum_residue_blocks,lpsQuadraticGauss_scaled_blocks]
  have hr (i : Fin m) (r : Fin d) :
      ((((r.val+d*i.val:ℕ):ZMod (d*m)).val):ZMod d)=(r.val:ZMod d) := by
    -- The chosen residue is below d*m, so the outer cast has this actual value.
    have hlt : r.val+d*i.val < d*m := by
      calc
        r.val+d*i.val < d+d*i.val := Nat.add_lt_add_right r.isLt _
        _ = d*(i.val+1) := by ring
        _ ≤ d*m := Nat.mul_le_mul_left d i.isLt
    rw [ZMod.val_natCast_of_lt hlt]
    simp
  simp_rw [hr]
  have hz (r : Fin d) : (r.val:ZMod d)=0 ↔ r=0 := by
    rw [lpsFin_cast_finEquiv]
    rw [← (ZMod.finEquiv d).map_zero]
    exact (ZMod.finEquiv d).injective.eq_iff
  simp_rw [hz]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,Fin.val_zero,
    zero_add,Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  congr 2
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
