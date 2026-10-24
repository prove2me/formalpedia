-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.proposition_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:05:40.974536+00:00
-- url     : https://prove2.me/submissions/5a28893b-494b-4d91-8bee-736445006fd3

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx in
theorem solution {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : κ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hbin : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hsum : ∀ ω, ∑ i, X i ω ≤ 1) :
    NegativelyAssociated X μ := by
  classical
  intro A B hAB f g hf hg hfm hgm hfb hgb
  set F : Ω → ℝ := fun ω => f (fun a => X a ω) with hFdef
  set G : Ω → ℝ := fun ω => g (fun b => X b ω) with hGdef
  set f0 := f 0
  set g0 := g 0
  have hnn : ∀ i ω, 0 ≤ X i ω := fun i ω => by rcases hbin i ω with h | h <;> rw [h] <;> norm_num
  -- if `X a ω = 1` then every other coordinate vanishes
  have hother : ∀ ω a b, a ≠ b → X a ω = 1 → X b ω = 0 := by
    intro ω a b hab ha
    have h2 : X a ω + X b ω ≤ ∑ i, X i ω := by
      rw [← Finset.sum_pair (f := fun i => X i ω) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hnn i ω)
    have := hsum ω
    rcases hbin b ω with h | h
    · exact h
    · linarith
  -- key pointwise identity: `(F - f0) (G - g0) = 0`
  have hkey : ∀ ω, (F ω - f0) * (G ω - g0) = 0 := by
    intro ω
    by_cases hA : ∀ a : A, X a ω = 0
    · have : (fun a : A => X a ω) = 0 := funext hA
      simp [hFdef, this, f0]
    · push Not at hA
      obtain ⟨a, ha⟩ := hA
      have ha1 : X a ω = 1 := (hbin a ω).resolve_left ha
      have hB : (fun b : B => X b ω) = 0 := by
        funext b
        have hab : (a : κ) ≠ b := by
          intro h
          exact Finset.disjoint_left.mp hAB a.2 (h ▸ b.2)
        exact hother ω a b hab ha1
      simp [hGdef, hB, g0]
  -- measurability and integrability
  have hFm : Measurable F :=
    hfm.comp (measurable_pi_lambda _ (fun a => hX a))
  have hGm : Measurable G :=
    hgm.comp (measurable_pi_lambda _ (fun b => hX b))
  have hFi : Integrable F μ := by
    obtain ⟨C, hC⟩ := hfb
    exact Integrable.of_bound hFm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hC _))
  have hGi : Integrable G μ := by
    obtain ⟨C, hC⟩ := hgb
    exact Integrable.of_bound hGm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hC _))
  -- monotonicity: `F ≥ f0`, `G ≥ g0`
  have hF0 : ∀ ω, f0 ≤ F ω := fun ω => hf (fun a => hnn a ω)
  have hG0 : ∀ ω, g0 ≤ G ω := fun ω => hg (fun b => hnn b ω)
  have hEF : f0 ≤ ∫ ω, F ω ∂μ := by
    have := integral_mono (integrable_const f0) hFi hF0
    simpa using this
  have hEG : g0 ≤ ∫ ω, G ω ∂μ := by
    have := integral_mono (integrable_const g0) hGi hG0
    simpa using this
  -- integrate the identity `F G = f0 G + g0 F - f0 g0`
  have hprod : (fun ω => F ω * G ω) = fun ω => f0 * G ω + g0 * F ω - f0 * g0 := by
    funext ω
    have := hkey ω
    linarith [this]
  have hint : ∫ ω, F ω * G ω ∂μ = f0 * ∫ ω, G ω ∂μ + g0 * ∫ ω, F ω ∂μ - f0 * g0 := by
    rw [hprod, integral_sub, integral_add, integral_const_mul, integral_const_mul]
    · simp
    · exact hGi.const_mul _
    · exact hFi.const_mul _
    · exact (hGi.const_mul _).add (hFi.const_mul _)
    · exact integrable_const _
  show ∫ ω, F ω * G ω ∂μ ≤ (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ
  rw [hint]
  nlinarith [mul_nonneg (sub_nonneg.mpr hEF) (sub_nonneg.mpr hEG)]
