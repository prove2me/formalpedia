-- Prove2me | solution 1 for P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:33.929439+00:00
-- url     : https://prove2.me/submissions/d1e4dd1c-972a-40b4-a6f1-4e33e5772b1b

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {d : ℕ} (t : Fin 1 → ℝ) : Measurable (fun x : Fin d → ℝ ↦ append x t) := by
  unfold append
  apply measurable_pi_lambda
  intro i
  split_ifs <;> fun_prop
end GaussianPerimeter.VolumeComparison
