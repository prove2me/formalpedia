-- Prove2me | solution 1 for SNumbers.Complexification.complexify_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:52.398969+00:00
-- url     : https://prove2.me/submissions/4e8e52b6-1c74-4485-b83f-5431d8c2dad9

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_snd
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
theorem _root_.solution (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    complexify S (conj u) = conj (complexify S u) := by
  apply Prod.ext <;> simp [map_neg]
end SNumbers.Complexification
