-- Prove2me | solution 1 for SellingData.AppendsBinary.deriv_alphaL
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:54.903191+00:00
-- url     : https://prove2.me/submissions/56e0366b-f5bb-4241-a911-93793fdd465d

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting
import Definitions.Def_SellingData_AppendsBinary_Setting
set_option autoImplicit false
open SellingData.AppendsBinary
open SellingData.AppendsBinary.Model

lemma jj_sv (φ α uLo uHi : ℝ) (hφ : 0 < φ) (hφ1 : φ < 1) (h0 : 0 < α) (h1 : α < 1) :
    SellingData.ListsBinary.sigmaH φ α *
        (SellingData.ListsBinary.phiH φ α * uHi + (1 - SellingData.ListsBinary.phiH φ α) * uLo)
      = φ * α * uHi + (1 - φ) * (1 - α) * uLo := by
  have hs : SellingData.ListsBinary.sigmaH φ α ≠ 0 := by
    have := mul_pos hφ h0
    have := mul_pos (sub_pos.2 hφ1) (sub_pos.2 h1)
    unfold SellingData.ListsBinary.sigmaH; linarith
  unfold SellingData.ListsBinary.phiH
  unfold SellingData.ListsBinary.sigmaH at hs ⊢
  field_simp
  ring

theorem solution (M : Model) (αH a k' : ℝ) (ha : a ∈ Set.Icc M.aLo M.aHi)
    (hk : HasDerivAt M.k k' a) :
    HasDerivAt (fun α => M.benchProfit SellingData.ListsBinary.CostType.L α)
        ((1 - M.θ) * (M.φ * (M.uHi - M.cL) - (1 - M.φ) * (M.uLo - M.cL) - k')) a ∧
      HasDerivAt (fun α => M.reducedProfit αH α)
        ((1 - M.θ) * (M.φ * (M.uHi - M.cL) - (1 - M.φ) * (M.uLo - M.cL) - k')
          + M.θ * (1 - 2 * M.φ) * (M.cL - M.cH)) a := by
  have h0 : 0 < a := by linarith [ha.1, M.half_lt_aLo]
  have h1 : a < 1 := by linarith [ha.2, M.aHi_lt_one]
  have hnb : Set.Ioo (0:ℝ) 1 ∈ nhds a := Ioo_mem_nhds h0 h1
  set C0 : ℝ := (1 - M.φ) * M.uLo - M.cL * (1 - M.φ) with hC0
  set C1 : ℝ := M.φ * M.uHi - (1 - M.φ) * M.uLo - M.cL * (M.φ - (1 - M.φ)) with hC1
  constructor
  · have hev : (fun α => (1 - M.θ) * ((C0 + C1 * α) - M.k α))
        =ᶠ[nhds a] (fun α => M.benchProfit SellingData.ListsBinary.CostType.L α) := by
      filter_upwards [hnb] with α hα
      have key := jj_sv M.φ α M.uLo M.uHi M.φ_pos M.φ_lt_one hα.1 hα.2
      simp only [Model.benchProfit, Model.σh, Model.vh, vHigh, Model.θi, Model.c]
      unfold SellingData.ListsBinary.sigmaH at key ⊢
      simp only [hC0, hC1]
      linear_combination (-(1 - M.θ)) * key
    have hd := ((((hasDerivAt_id' a).const_mul C1).const_add C0).sub hk).const_mul (1 - M.θ)
    refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [hC1]
    ring
  · set D0 : ℝ := M.θ * (M.σh αH * (M.vh αH - M.cH) - M.k αH) - M.uHat + M.cL with hD0
    set CC0 : ℝ := (1 - M.φ) * M.uLo - M.cL * (1 - M.φ) with hCC0
    have hev : (fun α => D0 + M.θ * (-(((1 - M.φ) + (2 * M.φ - 1) * α) * (M.cL - M.cH)))
          + (1 - M.θ) * ((CC0 + C1 * α) - M.k α))
        =ᶠ[nhds a] (fun α => M.reducedProfit αH α) := by
      filter_upwards [hnb] with α hα
      have key := jj_sv M.φ α M.uLo M.uHi M.φ_pos M.φ_lt_one hα.1 hα.2
      simp only [Model.reducedProfit, Model.σh, Model.vh, vHigh, hD0, hCC0, hC1]
      unfold SellingData.ListsBinary.sigmaH at key ⊢
      linear_combination (-(1 - M.θ)) * key
    have hs := ((((hasDerivAt_id' a).const_mul (2 * M.φ - 1)).const_add (1 - M.φ)).mul_const
      (M.cL - M.cH))
    have hd1 := (hs.neg).const_mul M.θ
    have hd2 := ((((hasDerivAt_id' a).const_mul C1).const_add CC0).sub hk).const_mul (1 - M.θ)
    have hd := ((hd1.const_add D0).add hd2)
    refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [hC1]
    ring
