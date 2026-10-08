-- Prove2me | solution 1 for SeatInventory.Nested.nested_ge_distinct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:03:32.281166+00:00
-- url     : https://prove2.me/submissions/33f18bd6-6dc4-491f-986a-5a34af0e8ee8

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

set_option autoImplicit false

namespace NGD18f

open SeatInventory.Nested

lemma key (f₁ f₂ : ℝ) (hf₁ : 0 ≤ f₁) (C S a b : ℕ) (hSC : S ≤ C) :
    distinctRevenue f₁ f₂ C S a b ≤ nestedRevenue f₁ f₂ C S a b := by
  unfold distinctRevenue nestedRevenue
  have h : (min a S : ℕ) ≤ min a (C - min b (C - S)) := by omega
  have h' : ((min a S : ℕ) : ℝ) ≤ ((min a (C - min b (C - S)) : ℕ) : ℝ) := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_left h' hf₁
  linarith

lemma key2 (f₁ f₂ : ℝ) (hf₁ : 0 ≤ f₁) (C S a b : ℕ) (hb : b < C - S) (ha : S < a) :
    distinctRevenue f₁ f₂ C S a b + f₁ ≤ nestedRevenue f₁ f₂ C S a b := by
  unfold distinctRevenue nestedRevenue
  have h : (min a S : ℕ) + 1 ≤ min a (C - min b (C - S)) := by omega
  have h' : ((min a S : ℕ) : ℝ) + 1 ≤ ((min a (C - min b (C - S)) : ℕ) : ℝ) := by
    exact_mod_cast h
  have := mul_le_mul_of_nonneg_left h' hf₁
  nlinarith

lemma absb (f : ℝ) (n C : ℕ) (h : n ≤ C) : ‖f * (n : ℝ)‖ ≤ |f| * C := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have : (n : ℝ) ≤ C := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_left this (abs_nonneg f)

lemma bound_nested (f₁ f₂ : ℝ) (C S a b : ℕ) :
    ‖nestedRevenue f₁ f₂ C S a b‖ ≤ |f₂| * C + |f₁| * C := by
  unfold nestedRevenue
  refine (norm_add_le _ _).trans (add_le_add (absb _ _ _ ?_) (absb _ _ _ ?_)) <;> omega

lemma bound_distinct (f₁ f₂ : ℝ) (C S a b : ℕ) (hSC : S ≤ C) :
    ‖distinctRevenue f₁ f₂ C S a b‖ ≤ |f₂| * C + |f₁| * C := by
  unfold distinctRevenue
  refine (norm_add_le _ _).trans (add_le_add (absb _ _ _ ?_) (absb _ _ _ ?_)) <;> omega

end NGD18f

open MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (f₁ f₂ : ℝ) (hf₁ : 0 ≤ f₁) (C S : ℕ) (hSC : S ≤ C) :
    SeatInventory.Nested.expectedDistinctRevenue μ r₁ r₂ f₁ f₂ C S ≤
        SeatInventory.Nested.expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S ∧
      (0 < f₁ → 0 < μ.real {ω | r₂ ω < C - S ∧ S < r₁ ω} →
        SeatInventory.Nested.expectedDistinctRevenue μ r₁ r₂ f₁ f₂ C S <
          SeatInventory.Nested.expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S) := by
  have hm : Measurable (fun ω => (r₁ ω, r₂ ω)) := hr₁.prodMk hr₂
  have intN : Integrable (fun ω => SeatInventory.Nested.nestedRevenue f₁ f₂ C S (r₁ ω) (r₂ ω)) μ := by
    refine Integrable.of_bound ?_ (|f₂| * C + |f₁| * C)
      (ae_of_all _ fun ω => NGD18f.bound_nested f₁ f₂ C S (r₁ ω) (r₂ ω))
    exact ((measurable_of_countable
      (fun p : ℕ × ℕ => SeatInventory.Nested.nestedRevenue f₁ f₂ C S p.1 p.2)).comp
        hm).aestronglyMeasurable
  have intD : Integrable (fun ω => SeatInventory.Nested.distinctRevenue f₁ f₂ C S (r₁ ω) (r₂ ω)) μ := by
    refine Integrable.of_bound ?_ (|f₂| * C + |f₁| * C)
      (ae_of_all _ fun ω => NGD18f.bound_distinct f₁ f₂ C S (r₁ ω) (r₂ ω) hSC)
    exact ((measurable_of_countable
      (fun p : ℕ × ℕ => SeatInventory.Nested.distinctRevenue f₁ f₂ C S p.1 p.2)).comp
        hm).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · exact integral_mono intD intN (fun ω => NGD18f.key f₁ f₂ hf₁ C S (r₁ ω) (r₂ ω) hSC)
  · intro hpos hA
    set A : Set Ω := {ω | r₂ ω < C - S ∧ S < r₁ ω} with hAdef
    have hAm : MeasurableSet A :=
      (hr₂ (MeasurableSet.of_discrete (s := {n : ℕ | n < C - S}))).inter
        (hr₁ (MeasurableSet.of_discrete (s := {n : ℕ | S < n})))
    have hle : ∀ ω, A.indicator (fun _ => f₁) ω ≤
        SeatInventory.Nested.nestedRevenue f₁ f₂ C S (r₁ ω) (r₂ ω) -
          SeatInventory.Nested.distinctRevenue f₁ f₂ C S (r₁ ω) (r₂ ω) := by
      intro ω
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        have := NGD18f.key2 f₁ f₂ hf₁ C S (r₁ ω) (r₂ ω) h.1 h.2
        linarith
      · rw [Set.indicator_of_notMem h]
        have := NGD18f.key f₁ f₂ hf₁ C S (r₁ ω) (r₂ ω) hSC
        linarith
    have hint := integral_mono ((integrable_const f₁).indicator hAm) (intN.sub intD) hle
    have hsub := integral_sub intN intD
    rw [integral_indicator_const _ hAm, smul_eq_mul] at hint
    simp only [Pi.sub_apply] at hint
    rw [hsub] at hint
    have : 0 < μ.real A * f₁ := mul_pos hA hpos
    unfold SeatInventory.Nested.expectedDistinctRevenue SeatInventory.Nested.expectedNestedRevenue
    linarith
