-- Prove2me | solution 1 for SellingData.AppendsBinary.willingness_to_pay
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:34:20.186979+00:00
-- url     : https://prove2.me/submissions/505a858c-902b-426b-987a-0dd31cf344e3

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

lemma jj_sl (φ α uLo uHi : ℝ) (hφ : 0 < φ) (hφ1 : φ < 1) (h0 : 0 < α) (h1 : α < 1) :
    SellingData.ListsBinary.sigmaL φ α *
        (SellingData.ListsBinary.phiL φ α * uHi + (1 - SellingData.ListsBinary.phiL φ α) * uLo)
      = φ * (1 - α) * uHi + (1 - φ) * α * uLo := by
  have hs : SellingData.ListsBinary.sigmaL φ α ≠ 0 := by
    have := mul_pos hφ (sub_pos.2 h1)
    have := mul_pos (sub_pos.2 hφ1) h0
    unfold SellingData.ListsBinary.sigmaL; linarith
  have hp : SellingData.ListsBinary.phiL φ α * SellingData.ListsBinary.sigmaL φ α
      = φ * (1 - α) := by
    unfold SellingData.ListsBinary.phiL SellingData.ListsBinary.sigmaL at hs ⊢
    exact div_mul_cancel₀ _ hs
  unfold SellingData.ListsBinary.sigmaL at hp ⊢
  linear_combination (uHi - uLo) * hp

theorem solution (M : Model) (hcH : M.cH < M.uHat) (m : Menu)
    (j : SellingData.ListsBinary.CostType)
    (hαj : m.α j ∈ Set.Icc M.aLo M.aHi) :
    (∀ i : SellingData.ListsBinary.CostType,
        M.U m i j - M.outside (M.c i) = -(m.T j) + M.σl (m.α j) * (M.c i - M.vl (m.α j))) ∧
      StrictMono (fun c : ℝ => -(m.T j) + M.σl (m.α j) * (c - M.vl (m.α j))) ∧
      M.U m SellingData.ListsBinary.CostType.L j - M.outside M.cL <
        M.U m SellingData.ListsBinary.CostType.H j - M.outside M.cH := by
  have h0 : 0 < m.α j := by linarith [hαj.1, M.half_lt_aLo]
  have h1 : m.α j < 1 := by linarith [hαj.2, M.aHi_lt_one]
  have hsl : 0 < M.σl (m.α j) := by
    have := mul_pos M.φ_pos (sub_pos.2 h1)
    have := mul_pos (sub_pos.2 M.φ_lt_one) h0
    simp only [Model.σl, SellingData.ListsBinary.sigmaL]; linarith
  have hcL : M.cL < M.uHat := lt_trans M.cL_lt_cH hcH
  have hout : ∀ i : SellingData.ListsBinary.CostType, M.outside (M.c i) = M.uHat - M.c i := by
    intro i
    have : M.c i < M.uHat := by
      cases i
      · exact hcH
      · exact hcL
    simp only [Model.outside]
    exact max_eq_left (by linarith)
  have hmain : ∀ i : SellingData.ListsBinary.CostType,
      M.U m i j - M.outside (M.c i) = -(m.T j) + M.σl (m.α j) * (M.c i - M.vl (m.α j)) := by
    intro i
    rw [hout i]
    have k1 := jj_sv M.φ (m.α j) M.uLo M.uHi M.φ_pos M.φ_lt_one h0 h1
    have k2 := jj_sl M.φ (m.α j) M.uLo M.uHi M.φ_pos M.φ_lt_one h0 h1
    simp only [Model.U, Model.payoff, Model.σh, Model.vh, vHigh, Model.σl, Model.vl, vLow,
      Model.uHat]
    simp only [SellingData.ListsBinary.sigmaH, SellingData.ListsBinary.sigmaL] at k1 k2 ⊢
    linear_combination k1 + k2
  refine ⟨hmain, ?_, ?_⟩
  · intro x y hxy
    have := mul_lt_mul_of_pos_left (sub_lt_sub_right hxy (M.vl (m.α j))) hsl
    simp only
    linarith
  · have hL : M.U m SellingData.ListsBinary.CostType.L j - M.outside M.cL =
        -(m.T j) + M.σl (m.α j) * (M.cL - M.vl (m.α j)) := hmain SellingData.ListsBinary.CostType.L
    have hH : M.U m SellingData.ListsBinary.CostType.H j - M.outside M.cH =
        -(m.T j) + M.σl (m.α j) * (M.cH - M.vl (m.α j)) := hmain SellingData.ListsBinary.CostType.H
    rw [hL, hH]
    have hc : M.cL < M.cH := M.cL_lt_cH
    have := mul_lt_mul_of_pos_left
      (sub_lt_sub_right hc (M.vl (m.α j))) hsl
    linarith
