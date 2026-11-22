-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_kleinAngle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:35.227987+00:00
-- url     : https://prove2.me/submissions/826dc5bf-53e0-4b47-bb38-e46f25f090a0

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_kleinInner
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    kleinAngle κ (shift κ a w P) (shift κ a w A) (shift κ a w B) = kleinAngle κ P A B := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hDP := shift_den_pos hκ ha hP
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hw4 : 0 < w ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring]
    exact pow_pos hw2 2
  have hm : 0 < w ^ 4 / (1 - κ * a * P.1) ^ 2 := div_pos hw4 (pow_pos hDP 2)
  have huv : 0 < 1 / (1 - κ * a * A.1) * (1 / (1 - κ * a * B.1)) :=
    mul_pos (one_div_pos.mpr hDA) (one_div_pos.mpr hDB)
  have e1 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) * (1 / (1 - κ * a * B.1))
        * kleinInner κ P A B := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDB.ne']
    field_simp
  have e2 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w A)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) ^ 2 * kleinInner κ P A A := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDA.ne']
    field_simp
  have e3 : kleinInner κ (shift κ a w P) (shift κ a w B) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * B.1)) ^ 2 * kleinInner κ P B B := by
    rw [shift_kleinInner hw hDP.ne' hDB.ne' hDB.ne']
    field_simp
  unfold kleinAngle
  rw [e1, e2, e3]
  exact kleinAngle_aux hm huv
end ParallelPostulate.HyperbolicPlane
