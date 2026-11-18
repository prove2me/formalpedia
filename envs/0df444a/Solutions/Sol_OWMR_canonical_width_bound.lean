-- Prove2me | solution 1 for OWMR.canonical_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:43:42.121921+00:00
-- url     : https://prove2.me/submissions/9059e355-e743-4930-a443-6e1866733541

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- A retailer's one-period demand has a finite first moment. -/
private lemma integrable_marginal {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

/-- The sum of `L` i.i.d. demands of a retailer is integrable. -/
private lemma integrable_sum {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin L => N.marginal i) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2
    (integrable_marginal N hN i)

theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    ENNReal.ofReal (N.h * N.p / (N.h + N.p) * (Sh - sh))
      ≤ ENNReal.ofReal (N.h * (N.H i + N.p) / (N.H i * (N.h + N.p))) * N.J i k := by
  obtain ⟨-, -, hs, hS, -⟩ := hcan
  have hh : 0 < N.h := hN.h_pos
  have hH : 0 < N.H i := hN.H_pos i
  have hp : 0 < N.p := hN.p_pos
  set π := Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i with hπ
  set μZ := ∫ z, ∑ j, (z j : ℝ) ∂π with hμZ
  have hu := integrable_sum N hN i (N.L i + 1)
  have hφ : ∀ y, Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 =>
      N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0) π := fun y =>
    (((integrable_const y).sub hu).pos_part.const_mul _).add
      ((hu.sub (integrable_const y)).pos_part.const_mul _)
  -- the two linear lower bounds on `F_i` (Jensen at the endpoints)
  have hlow1 : ∀ y, N.p * (μZ - y) ≤ N.F i y := by
    intro y
    have e : ∫ z, N.p * (∑ j, (z j : ℝ) - y) ∂π = N.p * (μZ - y) := by
      rw [integral_const_mul, integral_sub hu (integrable_const y), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    rw [← e]
    refine integral_mono ((hu.sub (integrable_const y)).const_mul _) (hφ y) fun z => ?_
    have h1 : 0 ≤ N.H i * max (y - ∑ j, (z j : ℝ)) 0 := mul_nonneg hH.le (le_max_right _ _)
    have h2 : N.p * (∑ j, (z j : ℝ) - y) ≤ N.p * max (∑ j, (z j : ℝ) - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp.le
    simp only
    linarith
  have hlow2 : ∀ y, N.H i * (y - μZ) ≤ N.F i y := by
    intro y
    have e : ∫ z, N.H i * (y - ∑ j, (z j : ℝ)) ∂π = N.H i * (y - μZ) := by
      rw [integral_const_mul, integral_sub (integrable_const y) hu, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    rw [← e]
    refine integral_mono (((integrable_const y).sub hu).const_mul _) (hφ y) fun z => ?_
    have h1 : 0 ≤ N.p * max (∑ j, (z j : ℝ) - y) 0 := mul_nonneg hp.le (le_max_right _ _)
    have h2 : N.H i * (y - ∑ j, (z j : ℝ)) ≤ N.H i * max (y - ∑ j, (z j : ℝ)) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hH.le
    simp only
    linarith
  have hF0 : 0 ≤ N.F i sh := integral_nonneg fun z =>
    add_nonneg (mul_nonneg hH.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
  have hJ : N.J i k = ENNReal.ofReal (N.F i sh) := hs.symm
  have hSle : N.F i Sh ≤ N.F i sh := by
    have hS' : ENNReal.ofReal (N.F i Sh) ≤ ENNReal.ofReal (N.F i sh) := by
      rw [← hJ]
      exact hS
    exact (ENNReal.ofReal_le_ofReal_iff hF0).1 hS'
  set G := N.F i sh with hG
  -- `p H (Ŝ - ŝ) ≤ (H + p) G`
  have core : N.p * N.H i * (Sh - sh) ≤ (N.H i + N.p) * G := by
    have a1 := hlow1 sh
    have a2 := hlow2 Sh
    nlinarith [mul_le_mul_of_nonneg_left a2 hp.le, mul_le_mul_of_nonneg_left a1 hH.le,
      mul_le_mul_of_nonneg_left hSle hp.le]
  rw [hJ, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have key1 : N.h * N.p / (N.h + N.p) * (Sh - sh)
      = N.h / ((N.h + N.p) * N.H i) * (N.p * N.H i * (Sh - sh)) := by
    field_simp
  have key2 : N.h * (N.H i + N.p) / (N.H i * (N.h + N.p)) * G
      = N.h / ((N.h + N.p) * N.H i) * ((N.H i + N.p) * G) := by
    field_simp
  rw [key1, key2]
  exact mul_le_mul_of_nonneg_left core (by positivity)
