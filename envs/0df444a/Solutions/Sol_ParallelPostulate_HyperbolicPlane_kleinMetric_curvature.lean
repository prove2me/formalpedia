-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinMetric_curvature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:54.280103+00:00
-- url     : https://prove2.me/submissions/87b99b34-c2dd-4852-843a-50844e2fed5a

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_cubic
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_sq
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_cube
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_det_three
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Filter Topology
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    gaussCurvature (kleinE κ) (kleinF κ) (kleinG κ) P = κ := by
  obtain ⟨x, y⟩ := P
  replace hP := mem_plane.mp hP
  simp only at hP
  have hB : 1 + κ * (x ^ 2 + y ^ 2) ≠ 0 := hP.ne'
  have bX : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (s ^ 2 + c ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have bY : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (c ^ 2 + s ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have hEx : partialX (kleinE κ) (x, y)
      = -4 * κ * x * (1 + κ * y ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinE
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * y ^ 2)
      (hasDerivAt_cubic (1 + κ * y ^ 2) 0 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hEy : partialY (kleinE κ) (x, y)
      = 2 * κ * y * (κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinE
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hFx : partialX (kleinF κ) (x, y)
      = κ * y * (3 * κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * s * y)
      (hasDerivAt_cubic 0 (-κ * y) 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hFy : partialY (kleinF κ) (x, y)
      = κ * x * (3 * κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * x * s)
      (hasDerivAt_cubic 0 (-κ * x) 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hGx : partialX (kleinG κ) (x, y)
      = 2 * κ * x * (κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinG
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hGy : partialY (kleinG κ) (x, y)
      = -4 * κ * y * (1 + κ * x ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinG
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * x ^ 2)
      (hasDerivAt_cubic (1 + κ * x ^ 2) 0 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have nX : ∀ᶠ t in 𝓝 x, 1 + κ * (t ^ 2 + y ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (t ^ 2 + y ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have nY : ∀ᶠ t in 𝓝 y, 1 + κ * (x ^ 2 + t ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (x ^ 2 + t ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have hEyy : partialY (partialY (kleinE κ)) (x, y)
      = ((2 * κ ^ 2 * x ^ 2 - 2 * κ - 6 * κ ^ 2 * y ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * y * ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * y - 2 * κ ^ 2 * y ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinE κ) (x, t)) =ᶠ[𝓝 y]
        fun t => ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (x ^ 2 + t ^ 2)) ^ 3 := by
      filter_upwards [nY] with t ht
      unfold partialY kleinE
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bY x t) ht).deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * x ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) y)
      (bY x y) hB).deriv).trans ?_
    ring
  have hGxx : partialX (partialX (kleinG κ)) (x, y)
      = ((2 * κ ^ 2 * y ^ 2 - 2 * κ - 6 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * x - 2 * κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialX (kleinG κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialX kleinG
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bX y t) ht).deriv).trans ?_
      ring
    unfold partialX at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * y ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hFxy : partialX (partialY (kleinF κ)) (x, y)
      = ((3 * κ ^ 2 * y ^ 2 - κ - 3 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((3 * κ ^ 2 * y ^ 2 - κ) * x - κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinF κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((3 * κ ^ 2 * y ^ 2 - κ) * t - κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialY kleinF
      refine ((hasDerivAt_div_sq (f := fun s => -κ * t * s)
        (hasDerivAt_cubic 0 (-κ * t) 0 0 (fun s => by ring) y) (bY t y) ht).deriv).trans ?_
      ring
    unfold partialX
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (3 * κ ^ 2 * y ^ 2 - κ) 0 (-κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hdet : kleinE κ (x, y) * kleinG κ (x, y) - kleinF κ (x, y) ^ 2
      = 1 / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    simp only [kleinE, kleinF, kleinG]
    field_simp
    ring
  unfold gaussCurvature
  rw [hdet, hEx, hEy, hFx, hFy, hGx, hGy, hEyy, hGxx, hFxy, det_three, det_three]
  simp only [kleinE, kleinF, kleinG]
  field_simp
  ring
end ParallelPostulate.HyperbolicPlane
