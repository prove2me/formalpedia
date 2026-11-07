-- Prove2me | solution 1 for StatUnlearn.gaussianReal_tof_comm
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T20:12:05.74105+00:00
-- url     : https://prove2.me/submissions/ae20a1e1-c4ec-432d-990d-626df1bc9801

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
import Theorems.Thm_StatUnlearn_tof_comm_of_map_involution
open MeasureTheory ProbabilityTheory
open StatUnlearn

theorem solution (μ ν : ℝ) (v : NNReal) :
    tof (gaussianReal μ v) (gaussianReal ν v) = tof (gaussianReal ν v) (gaussianReal μ v) := by
  funext t
  refine tof_comm_of_map_involution (fun x : ℝ => μ + ν - x) (fun x => by ring) (by fun_prop)
    (gaussianReal μ v) (gaussianReal ν v) ?_ ?_ t
  · have h : (fun x : ℝ => μ + ν - x) = (fun y => (μ + ν) + y) ∘ (fun x => -x) := by
      funext x; simp [sub_eq_add_neg]
    rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
      gaussianReal_map_const_add]
    simp
  · have h : (fun x : ℝ => μ + ν - x) = (fun y => (μ + ν) + y) ∘ (fun x => -x) := by
      funext x; simp [sub_eq_add_neg]
    rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
      gaussianReal_map_const_add]
    simp

