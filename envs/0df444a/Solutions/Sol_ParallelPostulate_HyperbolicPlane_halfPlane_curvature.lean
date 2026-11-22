-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.halfPlane_curvature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:59.858972+00:00
-- url     : https://prove2.me/submissions/42a34507-738d-483c-85c8-459d7ef49c91

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_sq
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_cube
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_det_three

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Filter Topology
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {p : ℝ × ℝ} (hp : 0 < p.2) :
    gaussCurvature (fun q => 1 / q.2 ^ 2) (fun _ => 0) (fun q => 1 / q.2 ^ 2) p = -1 := by
  obtain ⟨x, y⟩ := p
  simp only at hp
  have hEx : partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = 0 := by
    simp [partialX]
  have hEy : partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = -2 / y ^ 3 := by
    unfold partialY
    refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const y 1) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hExx : partialX (partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 0 := by
    simp [partialX]
  have hEyy : partialY (partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 6 / y ^ 4 := by
    have e : (fun t => partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, t)) =ᶠ[𝓝 y]
        fun t => -2 / t ^ 3 := by
      filter_upwards [eventually_gt_nhds hp] with t ht
      unfold partialY
      refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const t 1) (hasDerivAt_id' t)
        ht.ne').deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube (f := fun _ => -2) (hasDerivAt_const y (-2)) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hF : ∀ q : ℝ × ℝ, partialX (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 ∧
      partialY (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 := fun q => by simp [partialX, partialY]
  have hFxy : partialX (partialY (fun _ : ℝ × ℝ => (0 : ℝ))) (x, y) = 0 := by
    simp [partialX, partialY]
  unfold gaussCurvature
  rw [hEx, hEy, hExx, hEyy, (hF _).1, (hF _).2, hFxy, det_three, det_three]
  field_simp
  ring
end ParallelPostulate.HyperbolicPlane
