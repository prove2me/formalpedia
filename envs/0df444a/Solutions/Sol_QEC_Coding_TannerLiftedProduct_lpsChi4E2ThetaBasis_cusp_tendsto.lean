-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:22.583897+00:00
-- url     : https://prove2.me/submissions/c2eba784-cb9e-4b04-b731-3599a229afdb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_prime_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Dilate_cusp_coprime_tendsto


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsChi4E2ThetaBasis q b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
        lpsChi4EisensteinCuspConstant γ)) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hc := (((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_right.pow_right 2).pow_left b.val
  norm_num only [Nat.reducePow] at hc
  have h := lpsChi4E2Dilate_cusp_coprime_tendsto (q^b.val) (pow_pos (Fact.out : q.Prime).pos _) hc γ
  rw [lpsChi4E2Character_prime_pow q hq4 b.val,one_mul] at h
  exact h
end QEC.Coding.TannerLiftedProduct
