-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.hCls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:51.970145+00:00
-- url     : https://prove2.me/submissions/22349cbf-64f8-4d0d-b0e1-3054f611bff5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_det_line
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_det_sq_split
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_mX
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_mY


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution : HCls := by
  intro n s hs z m x v hx
  obtain ⟨h1, h2, h3⟩ := hx
  set c : ℂ := Complex.I * s with hc
  set M0 : Matrix (Fin n) (Fin n) ℂ := 1 - c • Matrix.of x
  set M0' : Matrix (Fin n) (Fin n) ℂ := 1 + c • Matrix.of x
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of v
  have hdM := det_line M0 (-c • V) h1
  have hdM' := det_line M0' (c • V) h2

  have e : (fun t : ℂ => clsC s z m 0 1 (x + t • v)) = fun t : ℂ =>
      Complex.exp (-z * Complex.log ((M0 + t • (-c • V)).det * (M0' + t • (c • V)).det)) * (((M0 + t • (-c • V)).det)⁻¹) ^ m := by
    funext t
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, mX, mY, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e]
  have hW0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det ∈ Complex.slitPlane := by
    have e0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det = (1 + Matrix.of x * Matrix.of x).det := by
      simp only [zero_smul, add_zero]
      exact (det_sq_split s hs x).symm
    rw [e0]
    exact h3
  have hW := hdM.fun_mul hdM'
  have hL := hW.clog (by simpa using hW0)
  have hE := (hL.const_mul (-z)).cexp
  have hD := (hdM.inv (by simpa using h1)).pow m
  have hT := hE.fun_mul hD
  refine hT.congr_deriv ?_
  simp only [zero_smul, add_zero]
  have hM0 : M0.det ≠ 0 := h1
  have hM0' : M0'.det ≠ 0 := h2
  have tr1 : (M0⁻¹ * (-c • V)).trace = -c * (Ym s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have tr2 : (M0'⁻¹ * (c • V)).trace = c * (Yp s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have ecls : clsC s z m 0 1 x = Complex.exp (-z * Complex.log (M0.det * M0'.det)) * (M0.det⁻¹) ^ m := by
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [ecls, tr1, tr2]
  simp only [Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    have hinv : M0.det * M0.det⁻¹ = 1 := mul_inv_cancel₀ hM0
    linear_combination (-(c * (Ym s x * V).trace * M0.det⁻¹ ^ k) * (1 + (k : ℂ))) * hinv
end PositivityTheory.Rg.Sw.SP
