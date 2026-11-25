-- Prove2me | solution 1 for P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:46:40.425651+00:00
-- url     : https://prove2.me/submissions/6dfa45b2-6a47-4ad4-a176-a9d6496ef9c5

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
omit [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (X : 𝔸) (c σ : ℝ) :
    HasDerivAt (fun σ : ℝ => exp ((c - σ) • X)) (-(exp ((c - σ) • X) * X)) σ := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (c - σ)).scomp σ
    ((hasDerivAt_id' σ).const_sub c)
  simpa [Function.comp_def] using h
end LieTrotter
