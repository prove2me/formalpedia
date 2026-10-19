-- Prove2me | solution 1 for OnlineNRM.TSFixed.integrable_lpObj_of_bounded_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T15:00:26.931624+00:00
-- url     : https://prove2.me/submissions/9c81f374-252b-47cd-a984-553fa6516cf6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP

open MeasureTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ}
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → Fin N → Fin K → ℝ)
    (hdmeas : ∀ i k, Measurable (fun ω => d ω i k))
    (hdBound : ∀ ω i k, d ω i k ∈ Set.Icc 0 (dbar i))
    (X : Ω → Fin K → ℝ) (hXmeas : Measurable X)
    (hX : ∀ᵐ ω ∂P, (∀ k, 0 ≤ X ω k) ∧ ∑ k : Fin K, X ω k ≤ 1) :
    Integrable (fun ω => lpObj p (d ω) (X ω)) P := by
  let C : ℝ := ∑ k : Fin K, ∑ i : Fin N, |p i k| * |dbar i|
  have hmeas : Measurable (fun ω => lpObj p (d ω) (X ω)) := by
    unfold lpObj
    fun_prop
  have hcoeff (ω : Ω) (k : Fin K) :
      |∑ i : Fin N, p i k * d ω i k| ≤ ∑ i : Fin N, |p i k| * |dbar i| := by
    calc
      |∑ i : Fin N, p i k * d ω i k| ≤ ∑ i : Fin N, |p i k * d ω i k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin N, |p i k| * |d ω i k| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
      _ ≤ ∑ i : Fin N, |p i k| * |dbar i| := by
        apply Finset.sum_le_sum
        intro i hi
        have hd0 : 0 ≤ d ω i k := (hdBound ω i k).1
        have hdb0 : 0 ≤ dbar i := le_trans hd0 (hdBound ω i k).2
        have hdabs : |d ω i k| ≤ |dbar i| := by
          rw [abs_of_nonneg hd0, abs_of_nonneg hdb0]
          exact (hdBound ω i k).2
        exact mul_le_mul_of_nonneg_left hdabs (abs_nonneg (p i k))
  have hterm (ω : Ω) (hkx : (∀ k, 0 ≤ X ω k) ∧ ∑ k : Fin K, X ω k ≤ 1) (k : Fin K) :
      |(∑ i : Fin N, p i k * d ω i k) * X ω k| ≤ ∑ i : Fin N, |p i k| * |dbar i| := by
    have hA : 0 ≤ ∑ i : Fin N, |p i k| * |dbar i| :=
      Finset.sum_nonneg fun i hi => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hxle : X ω k ≤ 1 := by
      exact le_trans
        (Finset.single_le_sum (fun j hj => hkx.1 j) (Finset.mem_univ k)) hkx.2
    calc
      |(∑ i : Fin N, p i k * d ω i k) * X ω k|
          = |∑ i : Fin N, p i k * d ω i k| * X ω k := by
              rw [abs_mul, abs_of_nonneg (hkx.1 k)]
      _ ≤ (∑ i : Fin N, |p i k| * |dbar i|) * X ω k :=
          mul_le_mul_of_nonneg_right (hcoeff ω k) (hkx.1 k)
      _ ≤ ∑ i : Fin N, |p i k| * |dbar i| := by
          nlinarith [mul_nonneg hA (sub_nonneg.mpr hxle)]
  have hbound : ∀ᵐ ω ∂P, ‖lpObj p (d ω) (X ω)‖ ≤ C := by
    filter_upwards [hX] with ω hω
    have hobj : |lpObj p (d ω) (X ω)| ≤ C := by
      rw [lpObj]
      dsimp [C]
      calc
        |∑ k : Fin K, (∑ i : Fin N, p i k * d ω i k) * X ω k|
            ≤ ∑ k : Fin K, |(∑ i : Fin N, p i k * d ω i k) * X ω k| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin K, ∑ i : Fin N, |p i k| * |dbar i| := by
              apply Finset.sum_le_sum
              intro k hk
              exact hterm ω hω k
    simpa [Real.norm_eq_abs] using hobj
  exact Integrable.of_bound hmeas.aestronglyMeasurable C hbound