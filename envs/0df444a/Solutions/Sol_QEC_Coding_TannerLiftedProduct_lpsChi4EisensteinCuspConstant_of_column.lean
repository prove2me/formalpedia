-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:55.309884+00:00
-- url     : https://prove2.me/submissions/bcbc3743-ac76-4bff-b4f9-62805cba7aef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCusp_denominator_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsInt_mod_eight_four_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsChi4EisensteinCuspConstant γ=
      if t=2 then 3*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*
        lpsChi4E2Character (((γ 0 0*(L:ℤ)):ℤ):ZMod 4) else 0 := by
  have h4 := lpsPrimePowerCusp_denominator_dvd 2 2 t L Nat.prime_two hL.coprime_two_left
  have h8 := lpsPrimePowerCusp_denominator_dvd 2 3 t L Nat.prime_two hL.coprime_two_left
  norm_num only [Int.reducePow] at h4 h8
  have hs : γ 1 0%8=4 ↔ t=2 := by
    rw [lpsInt_mod_eight_four_iff,hC,h4,h8]
    omega
  unfold lpsChi4EisensteinCuspConstant
  by_cases ht : t=2
  · subst t
    have hdiv : γ 1 0/4=(L:ℤ) := by rw [hC];norm_num
    rw [if_pos (hs.mpr rfl),if_pos rfl,hdiv]
  · rw [if_neg (fun h => ht (hs.mp h)),if_neg ht]
end QEC.Coding.TannerLiftedProduct
