-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P39.correlationMatrixLimits
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:26:09.411988+00:00
-- url     : https://prove2.me/submissions/4a0b9c75-e0ea-4678-b6f7-c56a30f2dda1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
open QAlgorithms.Papers.Independent.Advance50.P39
open Filter Topology

theorem solution {n : ℕ} (hn : 0 < n)
    (distance : Fin n → Fin n → ℝ) (hdiag : ∀ i, distance i i = 0)
    (hoffdiag : ∀ i j, i ≠ j → 0 < distance i j) :
    (∀ i j, Tendsto (fun radius => spatialCorrelation (distance i j) radius)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (if i = j then 1 else 0))) ∧
    (∀ i j, Tendsto (fun radius => spatialCorrelation (distance i j) radius)
      atTop (nhds 1)) := by
  constructor
  · intro i j
    by_cases h : i = j
    · subst h
      simp only [if_true, spatialCorrelation, hdiag, neg_zero, zero_div, Real.exp_zero]
      exact tendsto_const_nhds
    · simp only [h, if_false, spatialCorrelation]
      have hd := hoffdiag i j h
      have h1 : Tendsto (fun r : ℝ => distance i j * r⁻¹) (𝓝[>] 0) atTop :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop hd
      have h2 : Tendsto (fun r : ℝ => -(distance i j * r⁻¹)) (𝓝[>] 0) atBot :=
        tendsto_neg_atTop_atBot.comp h1
      have h3 := Real.tendsto_exp_atBot.comp h2
      refine h3.congr fun r => ?_
      simp only [Function.comp]
      congr 1
      ring
  · intro i j
    simp only [spatialCorrelation]
    have h1 : Tendsto (fun r : ℝ => -distance i j / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuous_exp.tendsto 0).comp h1
    rw [Real.exp_zero] at h2
    exact h2
