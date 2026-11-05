-- Prove2me | solution 1 for SLPricing.PreAnn.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:34:28.997098+00:00
-- url     : https://prove2.me/submissions/2a803a19-44f3-4a92-a2ba-ddf9340b38eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
import Theorems.Thm_SLPricing_PreAnn_example_2
import Theorems.Thm_SLPricing_PreAnn_proposition_1
import Theorems.Thm_SLPricing_PreAnn_proposition_2
import Theorems.Thm_SLPricing_PreAnn_preValue_continuous
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

open SLPricing.PreAnn

theorem solution (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δlp ∈ Ioc (0 : ℝ) 1, ∃ Δhp ∈ Ico (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) 1, (d ≤ Δlp ∨ Δhp ≤ d) →
      preValue (P.withδc d).noSL < preValue (P.withδc d) := by
  -- standing assumptions for every discount factor in [0,1]
  have hSt : ∀ d ∈ Icc (0 : ℝ) 1, (P.withδc d).Standing := fun d hd =>
    ⟨hP.σp_pos, hP.γ_nonneg, hd.1, hd.2, hP.c_nonneg, hP.c_lt_one⟩
  obtain ⟨V, hVc, hV⟩ := preValue_continuous P hP hγ
  -- the no-SL value from Proposition 1
  have hN : ∀ d ∈ Icc (0 : ℝ) 1,
      preValue (P.withδc d).noSL = (((1 - P.c) ^ 2 / (d + 3) : ℝ) : EReal) := fun d hd =>
    (proposition_1 (P.withδc d) (hSt d hd)).1
  set f : ℝ → ℝ := fun d => V d - (1 - P.c) ^ 2 / (d + 3) with hf
  have hfc : ContinuousOn f (Icc 0 1) := by
    refine hVc.sub ?_
    refine ContinuousOn.div continuousOn_const (continuousOn_id.add continuousOn_const) ?_
    intro x hx; linarith [hx.1]
  have key : ∀ d ∈ Icc (0 : ℝ) 1, 0 < f d →
      preValue (P.withδc d).noSL < preValue (P.withδc d) := by
    intro d hd h
    rw [hN d hd, hV d hd, EReal.coe_lt_coe_iff]
    simp only [hf] at h; linarith
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  -- δc = 0 : Example 2
  have f0 : 0 < f 0 := by
    have h := example_2 (P.withδc 0) (hSt 0 h0mem) hγ rfl
    rw [hN 0 h0mem, hV 0 h0mem, EReal.coe_lt_coe_iff] at h
    simp only [hf]; linarith
  -- δc = 1 : adoption inertia earns the no-SL optimum, but is strictly suboptimal (Prop. 2)
  have f1 : 0 < f 1 := by
    set Q := P.withδc 1 with hQ
    have hQs : Q.Standing := hSt 1 h1mem
    have hpv : prePost Q (mass ∅) = Measure.dirac 0 := by
      simp [prePost, preVar, mass, gaussianReal_zero_var]
    have hp2 : (0 : ℝ) ≤ (1 + P.c) / 2 := by linarith [hP.c_nonneg]
    have hp2' : (1 + P.c) / 2 ≤ 1 := by linarith [hP.c_lt_one]
    have hEq : IsPreEq Q 2 ((1 + P.c) / 2) ∅ := by
      refine ⟨MeasurableSet.empty, empty_subset _, fun x hx => absurd hx (notMem_empty x), ?_⟩
      intro x hx
      unfold DelaysPre
      have : 0 ≤ Q.δc * ∫ q, max (x + q - (1 + P.c) / 2) 0 ∂(prePost Q (mass ∅)) :=
        mul_nonneg hQs.δc_nonneg (integral_nonneg fun q => le_max_right _ _)
      linarith [hx.1.2]
    have hlate : lateMass ∅ ((1 + P.c) / 2) 0 = 1 - (1 + P.c) / 2 := by
      unfold lateMass
      have : {x ∈ Icc (0 : ℝ) 1 \ ∅ | (1 + P.c) / 2 ≤ x + 0} = Icc ((1 + P.c) / 2) 1 := by
        ext x; simp only [sdiff_empty, add_zero, mem_ofPred_eq, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨le_trans hp2 h1, h2⟩, h1⟩
      rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    have hprof : preProfit Q 2 ((1 + P.c) / 2) ∅ = (1 - P.c) ^ 2 / 4 := by
      unfold preProfit
      rw [hpv, integral_dirac, hlate]
      have : mass (∅ : Set ℝ) = 0 := by simp [mass]
      rw [this]
      have hc : Q.c = P.c := rfl
      rw [hc]; ring
    have hin : 1 - Q.δc < 2 - Q.δc * ((1 + P.c) / 2) := by
      have : Q.δc = 1 := rfl
      rw [this]; linarith [hP.c_lt_one]
    have h := (proposition_2 Q hQs hγ).1 2 ((1 + P.c) / 2) ∅ hEq hin
    rw [hprof, hV 1 h1mem, EReal.coe_lt_coe_iff] at h
    simp only [hf]; norm_num; linarith
  -- continuity carries the strict gaps to neighbourhoods of 0 and 1
  have ev0 : ∀ᶠ d in nhdsWithin (0 : ℝ) (Icc 0 1), 0 < f d :=
    (hfc 0 h0mem).eventually (lt_mem_nhds f0)
  have ev1 : ∀ᶠ d in nhdsWithin (1 : ℝ) (Icc 0 1), 0 < f d :=
    (hfc 1 h1mem).eventually (lt_mem_nhds f1)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 ev0
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhdsWithin_iff.1 ev1
  refine ⟨min (ε / 2) 1, ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩,
    max (1 - η / 2) 0, ⟨le_max_right _ _, max_lt (by linarith) one_pos⟩, ?_⟩
  intro d hd hor
  apply key d hd
  rcases hor with h | h
  · apply hεs
    refine ⟨?_, hd⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hd.1]
    have := min_le_left (ε / 2) 1
    linarith
  · apply hηs
    refine ⟨?_, hd⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hd.2])]
    have := le_max_left (1 - η / 2) 0
    linarith
