-- Prove2me | solution 1 for RQCMoments.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T05:55:53.890363+00:00
-- url     : https://prove2.me/submissions/e9b1df09-7653-42b0-9a55-b6f90f49a1a8

import Mathlib
import Theorems.Thm_RQCMoments_lemma_4_6

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

lemma maj_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (V : Polynomial ℝ) (hint : Integrable (fun t => V.eval t) μ)
    (hV : ∀ t, A.indicator (fun _ => (1 : ℝ)) t ≤ V.eval t) :
    (μ A).toReal ≤ ∫ t, V.eval t ∂μ := by
  have h1 : ∫ t, A.indicator (fun _ => (1 : ℝ)) t ∂μ = μ.real A := integral_indicator_one hA
  have h2 : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have h3 : ∫ t, A.indicator (fun _ => (1 : ℝ)) t ∂μ ≤ ∫ t, V.eval t ∂μ :=
    integral_mono h2 hint hV
  rw [h1] at h3
  simpa [Measure.real] using h3

theorem main (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (x : Fin ℓ → ℝ) (hx : StrictMono x) (w : Fin ℓ → ℝ)
    (hexact : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * ℓ - 2 →
      Integrable (fun t => g.eval t) μ ∧ ∫ t, g.eval t ∂μ = ∑ i, w i * g.eval (x i)) :
    ∀ i : Fin ℓ, (∑ j ∈ Finset.Iio i, w j) ≤ (μ (Set.Iic (x i))).toReal ∧
      (μ (Set.Iic (x i))).toReal ≤ ∑ j ∈ Finset.Iic i, w j := by
  classical
  intro i
  have hsum : ∑ j, w j = 1 := by
    have := (hexact (Polynomial.C 1) (by simp)).2
    simpa using this.symm
  constructor
  · obtain ⟨U, hdeg, hU1, hU2, -⟩ := lemma_4_6 ℓ (by omega) (fun k => -x (Fin.rev k))
      (by
        intro a b hab
        have := hx (Fin.rev_lt_rev.2 hab)
        simp only; linarith) i.rev
    set V : Polynomial ℝ := U.comp (-Polynomial.X) with hVdef
    have hVdeg : V.natDegree ≤ 2 * ℓ - 2 := by
      rw [hVdef, Polynomial.natDegree_comp]; simpa using hdeg
    have hVev : ∀ t, V.eval t = U.eval (-t) := by
      intro t; simp [hVdef, Polynomial.eval_comp]
    have hVx : ∀ j, V.eval (x j) = if i ≤ j then 1 else 0 := by
      intro j
      rw [hVev]
      have := hU2 j.rev
      simp only [Fin.rev_rev, Fin.rev_le_rev] at this
      exact this
    obtain ⟨hint, hI⟩ := hexact V hVdeg
    have hb := maj_bound μ (Set.Ici (x i)) measurableSet_Ici V hint (by
      intro t
      rw [hVev]
      have := hU1 (-t)
      simp only [neg_neg, Fin.rev_rev] at this
      by_cases h : x i ≤ t
      · have h' : -t ≤ -x i := by linarith
        simp only [Set.indicator, Set.mem_Ici, h, if_true]
        rw [if_pos h'] at this; exact this
      · simp only [Set.indicator, Set.mem_Ici, h, if_false]
        by_cases h' : -t ≤ -x i
        · rw [if_pos h'] at this; linarith
        · rw [if_neg h'] at this; linarith)
    rw [hI] at hb
    simp only [hVx, mul_ite, mul_one, mul_zero] at hb
    rw [← Finset.sum_filter] at hb
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => i ≤ j) w
    have hfil : Finset.univ.filter (fun j => ¬ i ≤ j) = Finset.Iio i := by
      ext j; simp
    rw [hfil, hsum] at hsplit
    have hcompl : μ (Set.Ici (x i))ᶜ = 1 - μ (Set.Ici (x i)) :=
      prob_compl_eq_one_sub measurableSet_Ici
    have hIio : (Set.Ici (x i))ᶜ = Set.Iio (x i) := by ext; simp
    have hle : (μ (Set.Iio (x i))).toReal ≤ (μ (Set.Iic (x i))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.Iio_subset_Iic_self)
    have hr : (μ (Set.Iio (x i))).toReal = 1 - (μ (Set.Ici (x i))).toReal := by
      rw [← hIio, hcompl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp
    linarith
  · obtain ⟨U, hdeg, hU1, hU2, -⟩ := lemma_4_6 ℓ (by omega) x hx i
    obtain ⟨hint, hI⟩ := hexact U hdeg
    have hb := maj_bound μ (Set.Iic (x i)) measurableSet_Iic U hint (by
      intro t; simpa [Set.indicator] using hU1 t)
    rw [hI] at hb
    refine hb.trans (le_of_eq ?_)
    simp only [hU2, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have : Finset.univ.filter (fun j => j ≤ i) = Finset.Iic i := by ext j; simp
    rw [this]

end RQCMoments

open RQCMoments in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (x : Fin ℓ → ℝ) (hx : StrictMono x) (w : Fin ℓ → ℝ)
    (hexact : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * ℓ - 2 →
      Integrable (fun t => g.eval t) μ ∧ ∫ t, g.eval t ∂μ = ∑ i, w i * g.eval (x i)) :
    ∀ i : Fin ℓ, (∑ j ∈ Finset.Iio i, w j) ≤ (μ (Set.Iic (x i))).toReal ∧
      (μ (Set.Iic (x i))).toReal ≤ ∑ j ∈ Finset.Iic i, w j :=
  main μ ℓ hℓ x hx w hexact
