-- Prove2me | solution 1 for P2M_Auto_hasDerivAt_gweight___b6d5e5597986
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:29.806981+00:00
-- url     : https://prove2.me/submissions/9aba101e-badc-4243-abb4-85ffa2b3f22f

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_gaussianD_variance

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (u : ι → ℝ) (h p : ℝ) {σ : ℝ} (hσ : 0 < σ) (i : ι) :
    HasDerivAt (fun τ => gweight u h τ p i) (h * gaussianD 2 σ (u i - p) / 2) σ := by
  have := (hasDerivAt_gaussianD_variance 0 hσ (u i - p)).const_mul h
  convert this using 1 <;> first | rfl | (simp [gweight, gaussianD_zero, Function.comp] <;> ring)
end Auto
