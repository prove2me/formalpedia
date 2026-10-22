-- Prove2me | solution 1 for SellingData.ListsBinary.reducedProfit_hasDerivAt_H
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:49.427301+00:00
-- url     : https://prove2.me/submissions/755f2574-1e07-496a-a4e0-51ed5ed8b05f

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting
set_option autoImplicit false
open SellingData.ListsBinary

lemma jj_sv (φ α uLo uHi : ℝ) (hφ : 0 < φ) (hφ1 : φ < 1) (h0 : 0 < α) (h1 : α < 1) :
    sigmaH φ α * (phiH φ α * uHi + (1 - phiH φ α) * uLo)
      = φ * α * uHi + (1 - φ) * (1 - α) * uLo := by
  have hs : sigmaH φ α ≠ 0 := by
    have := mul_pos hφ h0
    have := mul_pos (sub_pos.2 hφ1) (sub_pos.2 h1)
    unfold sigmaH; linarith
  unfold phiH
  unfold sigmaH at hs ⊢
  field_simp
  ring

theorem solution (S : Screening) (αL a k' : ℝ)
    (ha : a ∈ Set.Ioo S.aLo S.aHi) (hk : HasDerivAt S.k k' a) :
    HasDerivAt (fun α => S.reducedProfit α αL)
      (S.θ * (S.phi * (S.uHi - S.cH) - (1 - S.phi) * (S.uLo - S.cH) - k') +
        (1 - S.θ) * (1 - 2 * S.phi) * (S.cH - S.cL)) a := by
  have h0 : 0 < a := by linarith [ha.1, S.half_lt_aLo]
  have h1 : a < 1 := by linarith [ha.2, S.aHi_lt_one]
  set C0 : ℝ := (1 - S.phi) * S.uLo - S.cH * (1 - S.phi) with hC0
  set C1 : ℝ := S.phi * S.uHi - (1 - S.phi) * S.uLo - S.cH * (S.phi - (1 - S.phi)) with hC1
  set Z : ℝ := sigmaH S.phi αL * (vH S.uLo S.uHi S.phi αL - S.cL) - S.k αL with hZ
  have hev : (fun α => S.θ * ((C0 + C1 * α) - S.k α) +
        (1 - S.θ) * (Z - (((1 - S.phi) + (2 * S.phi - 1) * α)) * (S.cH - S.cL)))
      =ᶠ[nhds a] (fun α => S.reducedProfit α αL) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with α hα
    have key := jj_sv S.phi α S.uLo S.uHi S.phi_pos S.phi_lt_one hα.1 hα.2
    simp only [Screening.reducedProfit, vH, hZ]
    unfold sigmaH at key ⊢
    simp only [hC0, hC1]
    linear_combination (-S.θ) * key
  have hd1 := ((((hasDerivAt_id' a).const_mul C1).const_add C0).sub hk).const_mul S.θ
  have hs := ((((hasDerivAt_id' a).const_mul (2 * S.phi - 1)).const_add (1 - S.phi)).mul_const
    (S.cH - S.cL))
  have hd2 := (hs.const_sub Z).const_mul (1 - S.θ)
  refine ((hd1.add hd2).congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [hC1]
  ring
