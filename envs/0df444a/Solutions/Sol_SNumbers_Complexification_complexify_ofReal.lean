-- Prove2me | solution 1 for SNumbers.Complexification.complexify_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:42.168221+00:00
-- url     : https://prove2.me/submissions/c7642e32-05ad-4fbc-9a1f-81543820560c

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_snd

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
theorem _root_.solution (S : H₁ →L[ℝ] H₂) (x : H₁) :
    complexify S (ofReal x) = ofReal (S x) := by
  apply Prod.ext <;> simp
end SNumbers.Complexification
