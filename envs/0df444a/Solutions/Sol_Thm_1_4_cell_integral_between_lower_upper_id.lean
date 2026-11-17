-- Prove2me | solution 1 for Thm_1_4.cell_integral_between_lower_upper_id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:22.663242+00:00
-- url     : https://prove2.me/submissions/99aac004-568d-44fe-84f1-9bd5fa4b741e

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set DarbouxRS MeasureTheory
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_cell_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) (i : Fin P.n) :
    lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x ∧
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x ≤
        upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
  have huv : P.pts i.castSucc ≤ P.pts i.succ :=
    le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
  have hgcell :
      ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
    hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
  have hgi : IntervalIntegrable g MeasureTheory.volume (P.pts i.castSucc) (P.pts i.succ) :=
    ContinuousOn.intervalIntegrable_of_Icc huv hgcell
  have hconstLower :
      IntervalIntegrable (fun _ : ℝ => lowerStep P g i) MeasureTheory.volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hconstUpper :
      IntervalIntegrable (fun _ : ℝ => upperStep P g i) MeasureTheory.volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hcellBelow : BddBelow (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddBelow
  have hcellAbove : BddAbove (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddAbove
  have hLowerPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        lowerStep P g i ≤ g x := by
    intro x hx
    unfold lowerStep
    exact csInf_le hcellBelow ⟨x, hx, rfl⟩
  have hUpperPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        g x ≤ upperStep P g i := by
    intro x hx
    unfold upperStep
    exact le_csSup hcellAbove ⟨x, hx, rfl⟩
  have hLowerIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x :=
    intervalIntegral.integral_mono_on huv hconstLower hgi hLowerPoint
  have hUpperIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, g x) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
    intervalIntegral.integral_mono_on huv hgi hconstUpper hUpperPoint
  constructor
  · calc
      lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)
          = ∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, g x := hLowerIntegral
  · calc
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x
          ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
            hUpperIntegral
      _ = upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) (i : Fin P.n) :
    lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x ∧
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x ≤
        upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
  exact source_cell_integral_between_lower_upper_id hg P i
