-- Prove2me | solution 1 for ProbabilityTheory.condExp_simplex_ae
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:31:39.585468+00:00
-- url     : https://prove2.me/submissions/59fe4e6d-2e9c-4594-89f3-90698e5434da

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory
open scoped BigOperators

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hw1 : ∀ ω, ∑ a : α, w ω a = 1) :
    (∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => (P[fun ω' => w ω' a | m]) ω)) ∧
      (∀ᵐ ω ∂P, ∀ a, 0 ≤ (P[fun ω' => w ω' a | m]) ω) ∧
        (∀ᵐ ω ∂P, ∑ a : α, (P[fun ω' => w ω' a | m]) ω = 1) := by
  have hle : ∀ ω a, w ω a ≤ 1 := by
    intro ω a
    calc
      w ω a ≤ ∑ b : α, w ω b :=
        Finset.single_le_sum (fun b hb => hw0 ω b) (Finset.mem_univ a)
      _ = 1 := hw1 ω
  have hint : ∀ a, Integrable (fun ω => w ω a) P := by
    intro a
    apply (integrable_const (μ := P) (1 : ℝ)).mono'
    · exact (hw a).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ω a)]
      exact hle ω a
  have hnonneg : ∀ a, 0 ≤ᵐ[P] P[fun ω' => w ω' a | m] := by
    intro a
    exact condExp_nonneg (μ := P) (m := m) (f := fun ω => w ω a)
      (Filter.Eventually.of_forall (hw0 · a))
  have hsum : (fun ω => ∑ a : α, w ω a) = fun _ => (1 : ℝ) := by
    funext ω
    exact hw1 ω
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (stronglyMeasurable_condExp (μ := P) (m := m)
      (f := fun ω => w ω a)).measurable.mono hm le_rfl
  · exact ae_all_iff.mpr hnonneg
  · have hce := condExp_finsetSum (μ := P) (m := m)
      (s := Finset.univ) (f := fun a ω => w ω a) (by
        intro a ha
        exact hint a)
    have hce' : P[fun ω => ∑ a : α, w ω a | m] =ᵐ[P]
        fun ω => ∑ a : α, (P[fun ω' => w ω' a | m]) ω := by
      simpa only [Finset.sum_fn] using hce
    have hconst : P[fun _ : Ω => (1 : ℝ) | m] = fun _ => (1 : ℝ) := by
      exact condExp_const (μ := P) hm 1
    have hleft : P[fun ω => ∑ a : α, w ω a | m] = fun _ => (1 : ℝ) := by
      rw [hsum]
      exact hconst
    filter_upwards [hce', Filter.Eventually.of_forall fun ω => congrFun hleft ω]
      with ω h_eq h_one
    calc
      (∑ a : α, (P[fun ω' => w ω' a | m]) ω) =
          (P[fun ω => ∑ a : α, w ω a | m]) ω := h_eq.symm
      _ = 1 := h_one
