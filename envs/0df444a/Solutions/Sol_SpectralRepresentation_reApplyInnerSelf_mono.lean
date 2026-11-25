-- Prove2me | solution 1 for SpectralRepresentation.reApplyInnerSelf_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:45.794207+00:00
-- url     : https://prove2.me/submissions/bad175da-56ae-4b44-931b-e487fed54cc9

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
section
@[expose] public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
namespace SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- `re⟪(B - C) x, x⟫` splits additively over the difference. -/
private theorem reApplyInnerSelf_sub (B C : H →L[ℂ] H) (x : H) :
    (B - C).reApplyInnerSelf x = B.reApplyInnerSelf x - C.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub]
end SpectralRepresentation
end
end

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
omit [CompleteSpace H] [Nontrivial H]
namespace SpectralRepresentation
theorem _root_.solution {B C : H →L[ℂ] H} (h : B ≤ C) (x : H) :
    B.reApplyInnerSelf x ≤ C.reApplyInnerSelf x := by
  have hpos : (C - B).IsPositive := h
  have h2 := hpos.2 x
  rw [reApplyInnerSelf_sub, sub_nonneg] at h2
  exact h2
end SpectralRepresentation
