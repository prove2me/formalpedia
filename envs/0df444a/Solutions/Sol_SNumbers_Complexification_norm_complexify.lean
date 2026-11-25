-- Prove2me | solution 1 for SNumbers.Complexification.norm_complexify
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:40:01.073904+00:00
-- url     : https://prove2.me/submissions/5ee2af81-98a1-42a9-8a5c-c96c25771c92

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_ofReal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open RCLike Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open SNumbers
open SNumbers.Complexification
variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
namespace SNumbers.Complexification
theorem _root_.solution (S : H₁ →L[ℝ] H₂) : ‖complexify S‖ = ‖S‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) (norm_complexifyₗ_le S)
  · refine ContinuousLinearMap.opNorm_le_bound S (norm_nonneg (complexify S)) fun x => ?_
    calc ‖S x‖ = ‖complexify S (ofReal x)‖ := by rw [complexify_ofReal, norm_ofReal]
      _ ≤ ‖complexify S‖ * ‖ofReal x‖ := (complexify S).le_opNorm _
      _ = ‖complexify S‖ * ‖x‖ := by rw [norm_ofReal]
end SNumbers.Complexification
