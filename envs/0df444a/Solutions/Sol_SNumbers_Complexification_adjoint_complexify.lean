-- Prove2me | solution 1 for SNumbers.Complexification.adjoint_complexify
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:58.446703+00:00
-- url     : https://prove2.me/submissions/6c654379-9bec-48eb-9aaf-c3b63d8fcfcb

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.norm_complexify

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
variable [CompleteSpace H₁] [CompleteSpace H₂]
namespace SNumbers.Complexification
theorem _root_.solution (S : H₁ →L[ℝ] H₂) :
    ContinuousLinearMap.adjoint (complexify S) = complexify (ContinuousLinearMap.adjoint S) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  apply Complex.ext <;>
    simp only [inner_re, inner_im, complexify_fst, complexify_snd,
      ContinuousLinearMap.adjoint_inner_left]
end SNumbers.Complexification
