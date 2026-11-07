-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_even_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:25.623192+00:00
-- url     : https://prove2.me/submissions/573ee48d-7ba0-45fa-a19b-7419eeef8dc0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_of_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N s k : ℕ) [NeZero N] (hN : N=4*s*k)
    (hk : 0 < k) (a n : ℤ) (hn : ¬ (2*(s:ℤ)) ∣ n) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) = 0 := by
  let t : ZMod N := (2*k:ℕ)
  have hc : (4:ZMod N)*(s:ZMod N)*(k:ZMod N)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (show ((4*s*k:ℕ):ZMod N)=0 by rw [← hN];exact ZMod.natCast_self N)
  have hl : 2*(((s:ℤ)*a:ℤ):ZMod N)*t=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (a:ZMod N)*((4:ZMod N)*(s:ZMod N)*(k:ZMod N)) := by ring
      _ = 0 := by rw [hc,mul_zero]
  have hq : (((s:ℤ)*a:ℤ):ZMod N)*t^2=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (a:ZMod N)*(k:ZMod N)*((4:ZMod N)*(s:ZMod N)*(k:ZMod N)) := by ring
      _ = 0 := by rw [hc,mul_zero]
  apply lpsQuadraticFourier_zero_of_translation N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) t hl hq
  intro he
  have ht : ((n*(2*(k:ℤ)):ℤ):ZMod N)=0 := by
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat,t] using he
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ht
  have hcI : (N:ℤ)=(2*(k:ℤ))*(2*(s:ℤ)) := by rw [hN];push_cast;ring
  rw [hcI,mul_comm n (2*(k:ℤ))] at hd
  have hkn : 2*(k:ℤ)≠0 := by positivity
  exact hn ((mul_dvd_mul_iff_left hkn).mp hd)
end QEC.Coding.TannerLiftedProduct
