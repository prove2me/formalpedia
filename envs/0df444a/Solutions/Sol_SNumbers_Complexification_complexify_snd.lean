-- Prove2me | solution 1 for SNumbers.Complexification.complexify_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:31:06.965603+00:00
-- url     : https://prove2.me/submissions/4ce39eaf-dce6-4224-ba41-e3e1fc5a7c9d

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification

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
    (complexify S u).2 = S u.2 := rfl
end SNumbers.Complexification
