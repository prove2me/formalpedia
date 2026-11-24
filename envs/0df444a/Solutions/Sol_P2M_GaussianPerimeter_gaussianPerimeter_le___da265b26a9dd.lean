-- Prove2me | solution 1 for P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:43.047987+00:00
-- url     : https://prove2.me/submissions/0a821a58-e1e7-4f89-b47d-b65a1a7ea7e1

module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_Definitions

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Convex ℝ K) : gaussianPerimeter K ≤ Γ n :=
  le_iSup₂ (f := fun K _ => gaussianPerimeter K) K hK
end GaussianPerimeter
