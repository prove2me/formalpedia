-- Prove2me | solution 1 for Thm_1_4.rsTaggedCommonLimit_derivative_of_identity_tagged_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:20:48.868653+00:00
-- url     : https://prove2.me/submissions/42db9959-7d54-4a5b-9c9a-0ce066e891fe

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_taggedSum_derivative_identity_abs_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    {f α α' : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b))
    (hId : rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x) L) :
    rsTaggedCommonLimit a b f α L := by
  refine ⟨sourceHypotheses_of_continuous_derivative_integrator hab hf hαmono, ?_⟩
  intro eps heps
  rcases exists_pos_abs_bound_of_continuousOn hf with ⟨C, hCpos, hCbound⟩
  let eta : ℝ := eps / (4 * C * (b - a))
  have hspan_pos : 0 < b - a := sub_pos.mpr hab
  have hden_pos : 0 < 4 * C * (b - a) := by positivity
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hdiff_budget : C * eta * (b - a) < eps / 2 := by
    have hcalc : C * eta * (b - a) = eps / 4 := by
      dsimp [eta]
      field_simp [ne_of_gt hCpos, ne_of_gt hspan_pos]
    linarith
  have hunif : UniformContinuousOn α' (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hα'cont
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δA, hδApos, HδA⟩
  rcases hId with ⟨_hsId, hlimId⟩
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimId (eps / 2) hhalf with ⟨δI, hδIpos, HδI⟩
  refine ⟨min δA δI, lt_min hδApos hδIpos, ?_⟩
  intro P tags htags hmesh
  have hmeshA : P.mesh < δA := lt_of_lt_of_le hmesh (min_le_left δA δI)
  have hmeshI : P.mesh < δI := lt_of_lt_of_le hmesh (min_le_right δA δI)
  have hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < δA → |α' x - α' y| ≤ eta := by
    intro x hx y hy hxy
    have hdist : dist x y < δA := by
      simpa [Real.dist_eq] using hxy
    have h := HδA x hx y hy hdist
    exact le_of_lt (by simpa [Real.dist_eq] using h)
  let Sid : ℝ := taggedSum P tags (fun x => f x * α' x) (fun x => x)
  have hdiff :
      |taggedSum P tags f α - Sid| < eps / 2 := by
    have hle :
        |taggedSum P tags f α - Sid| ≤ C * eta * (b - a) := by
      simpa [Sid] using
        taggedSum_derivative_identity_abs_le
          (f := f) (α := α) (α' := α') (a := a) (b := b)
          (C := C) (eta := eta) (delta := δA)
          P tags htags hαderiv hα'osc hmeshA hCbound (le_of_lt hCpos)
    exact lt_of_le_of_lt hle hdiff_budget
  have hIdClose : |Sid - L| < eps / 2 := by
    simpa [Sid] using HδI P tags htags hmeshI
  have htriangle :
      |taggedSum P tags f α - L| ≤
        |taggedSum P tags f α - Sid| + |Sid - L| := by
    have hdecomp :
        taggedSum P tags f α - L =
          (taggedSum P tags f α - Sid) + (Sid - L) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |taggedSum P tags f α - L|
        ≤ |taggedSum P tags f α - Sid| + |Sid - L| := htriangle
    _ < eps / 2 + eps / 2 := add_lt_add hdiff hIdClose
    _ = eps := by ring

theorem solution
    {f α α' : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b))
    (hId : rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x) L) :
    rsTaggedCommonLimit a b f α L := by
  exact source_rsTaggedCommonLimit_derivative_of_identity_tagged_limit hab hf hαmono hαderiv hα'cont hId
