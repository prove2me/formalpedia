-- Prove2me | solution 1 for StochIneqPO.DBar.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:28:27.933145+00:00
-- url     : https://prove2.me/submissions/7ea93b94-12cb-4129-b825-f7dc0c7c5d5d

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar
import Definitions.Def_StochIneqPO_DBar_meetPath
import Theorems.Thm_StochIneqPO_DBar_lemma3_dbar_eq_of_le
import Theorems.Thm_StochIneqPO_DBar_dbar_triangle
import Theorems.Thm_StochIneqPO_DBar_dbar_attained
import Theorems.Thm_StochIneqPO_DBar_meet_pushforward_le

open MeasureTheory StochIneqPO.DBar

theorem dbar_symm_aux (P Q : Measure (ℤ → ℝ)) :
    StochIneqPO.DBar.dbar P Q = StochIneqPO.DBar.dbar Q P := by
  have hshift : Measurable (StochIneqPO.DBar.shift (E := ℝ)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  have key : ∀ P Q : Measure (ℤ → ℝ),
      {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
        IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
        c = ∫ z, |z.1 0 - z.2 0| ∂ν} ⊆
      {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
        IsPairShiftInvariant ν ∧ ν.map Prod.fst = Q ∧ ν.map Prod.snd = P ∧
        c = ∫ z, |z.1 0 - z.2 0| ∂ν} := by
    intro P Q c ⟨ν, ⟨hprob, hinv⟩, h1, h2, hc⟩
    refine ⟨ν.map Prod.swap, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
    · rw [Measure.map_map (hshift.prodMap hshift) measurable_swap]
      have : (Prod.map (StochIneqPO.DBar.shift (E := ℝ)) (StochIneqPO.DBar.shift (E := ℝ)))
          ∘ Prod.swap = Prod.swap ∘ (Prod.map (StochIneqPO.DBar.shift (E := ℝ))
            (StochIneqPO.DBar.shift (E := ℝ))) := by
        funext z; rfl
      rw [this, ← Measure.map_map measurable_swap (hshift.prodMap hshift), hinv]
    · rw [Measure.map_map measurable_fst measurable_swap]; exact h2
    · rw [Measure.map_map measurable_snd measurable_swap]; exact h1
    · rw [hc, integral_map measurable_swap.aemeasurable]
      · simp only [Prod.fst_swap, Prod.snd_swap]
        congr 1; funext z; exact abs_sub_comm _ _
      · exact (Measurable.aestronglyMeasurable (by fun_prop))
  unfold StochIneqPO.DBar.dbar
  rw [Set.Subset.antisymm (key P Q) (key Q P)]

theorem solution
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    ∃ s : ℝ,
      IsLUB {r : ℝ | ∃ R : Measure (ℤ → ℝ),
        IsShiftInvariant R ∧ Integrable (fun ω : ℤ → ℝ => ω 0) R ∧
        StochIneqPO.Comparison.StochLE R P ∧ StochIneqPO.Comparison.StochLE R Q ∧ r = ∫ ω, ω 0 ∂ R} s ∧
      dbar P Q = (∫ ω, ω 0 ∂P) + (∫ ω, ω 0 ∂Q) - 2 * s := by
  obtain ⟨ν, hν, hν1, hν2, hd⟩ := dbar_attained P Q hP hQ hPi hQi
  obtain ⟨hR', hR'P, hR'Q⟩ := meet_pushforward_le P Q ν hν hν1 hν2
  have := hν.1
  have hmeet : Measurable meetPath :=
    measurable_pi_lambda _ (fun n =>
      ((measurable_pi_apply n).comp measurable_fst).min ((measurable_pi_apply n).comp measurable_snd))
  have h0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
  -- integrability of the coordinates under ν
  have hI1 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.1 0) ν := by
    rw [← hν1] at hPi
    exact (integrable_map_measure h0.aestronglyMeasurable measurable_fst.aemeasurable).mp hPi
  have hI2 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0) ν := by
    rw [← hν2] at hQi
    exact (integrable_map_measure h0.aestronglyMeasurable measurable_snd.aemeasurable).mp hQi
  have hImin : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => min (z.1 0) (z.2 0)) ν := by
    refine Integrable.mono' (hI1.abs.add hI2.abs) ?_ ?_
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rcases min_choice (z.1 0) (z.2 0) with h | h <;> rw [h] <;>
        linarith [abs_nonneg (z.1 0), abs_nonneg (z.2 0)]
  have hR'i : Integrable (fun ω : ℤ → ℝ => ω 0) (ν.map meetPath) :=
    (integrable_map_measure h0.aestronglyMeasurable hmeet.aemeasurable).mpr hImin
  have hER' : ∫ ω, ω 0 ∂(ν.map meetPath) = ∫ z, min (z.1 0) (z.2 0) ∂ν := by
    rw [integral_map hmeet.aemeasurable h0.aestronglyMeasurable]; rfl
  have hEP : ∫ ω, ω 0 ∂P = ∫ z, z.1 0 ∂ν := by
    rw [← hν1, integral_map measurable_fst.aemeasurable h0.aestronglyMeasurable]
  have hEQ : ∫ ω, ω 0 ∂Q = ∫ z, z.2 0 ∂ν := by
    rw [← hν2, integral_map measurable_snd.aemeasurable h0.aestronglyMeasurable]
  have hdval : dbar P Q = (∫ ω, ω 0 ∂P) + (∫ ω, ω 0 ∂Q) - 2 * ∫ ω, ω 0 ∂(ν.map meetPath) := by
    rw [hd, hER', hEP, hEQ, ← integral_add hI1 hI2, ← integral_const_mul,
      ← integral_sub (f := fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.1 0 + z.2 0) (hI1.add hI2)
        (hImin.const_mul 2)]
    congr 1; funext z
    rcases le_total (z.1 0) (z.2 0) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  refine ⟨∫ ω, ω 0 ∂(ν.map meetPath), ⟨?_, ?_⟩, hdval⟩
  · intro r ⟨R, hR, hRi, hRP, hRQ, hr⟩
    have h1 := lemma3_dbar_eq_of_le R P hR hP hRi hPi hRP
    have h2 := lemma3_dbar_eq_of_le R Q hR hQ hRi hQi hRQ
    have htri := dbar_triangle P Q R hP hQ hR hPi hQi hRi
    rw [dbar_symm_aux P R, h1, h2, hdval] at htri
    rw [hr]; linarith
  · intro b hb
    exact hb ⟨ν.map meetPath, hR', hR'i, hR'P, hR'Q, rfl⟩
