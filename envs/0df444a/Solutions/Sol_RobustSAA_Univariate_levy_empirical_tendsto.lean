-- Prove2me | solution 1 for RobustSAA.Univariate.levy_empirical_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:05:18.153051+00:00
-- url     : https://prove2.me/submissions/39b8ec18-b2fb-4dac-a23f-0c1abef99d66

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting
import Theorems.Thm_GlivenkoCantelli_glivenko_cantelli

open Filter MeasureTheory ProbabilityTheory RobustSAA.Univariate

namespace RSAA3LE

lemma card_sample_eq (ω : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (Finset.univ.filter (fun i : Fin N => sample ω N i ≤ x)).card =
      ((Finset.range N).filter (fun i => ω i ≤ x)).card := by
  refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    have hi' : ω i ≤ x := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi'⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩, rfl⟩

lemma levy_le_sup (A B : ℝ → ℝ) (hA : Monotone A) (hB : Monotone B) (S : ℝ)
    (hS : ∀ x, |A x - B x| ≤ S) : levyDist A B ≤ S := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  apply csInf_le ⟨0, fun _ h => le_of_lt h.1⟩
  refine ⟨by linarith, fun ξ => ⟨?_, ?_⟩⟩
  · have h1 := (abs_le.mp (hS (ξ - (S + δ)))).2
    have h2 := hB (show ξ - (S + δ) ≤ ξ by linarith)
    linarith
  · have h1 := (abs_le.mp (hS ξ)).1
    have h2 := hA (show ξ ≤ ξ + (S + δ) by linarith)
    linarith

lemma empCdf_mono {N : ℕ} (s : Fin N → ℝ) : Monotone (empCdf s) := by
  intro a b hab
  unfold empCdf
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi hab)

end RSAA3LE

open RSAA3LE

theorem solution (F : ProbabilityMeasure ℝ) (hF : IsContinuousLaw F) :
    ∀ᵐ ω ∂dataLaw F,
      Tendsto (fun N => levyDist (empCdf (sample ω N)) (cdfOf F)) atTop (nhds 0) := by
  set P := dataLaw F with hP
  have hprob : IsProbabilityMeasure P := by
    rw [hP]; unfold dataLaw; infer_instance
  have hmeas : ∀ i, Measurable (fun ω : ℕ → ℝ => ω i) := fun i => measurable_pi_apply i
  have hind : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) P := by
    rw [hP]; unfold dataLaw
    exact iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure ℝ)) (X := fun _ => id)
      (fun _ => measurable_id)
  have hmap : ∀ i, P.map (fun ω : ℕ → ℝ => ω i) = (F : Measure ℝ) := by
    intro i; rw [hP]; unfold dataLaw
    exact Measure.infinitePi_map_eval _ i
  have hident : ∀ i, IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0) P P := by
    intro i
    exact ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hmap, hmap]⟩
  have hGC := GlivenkoCantelli.glivenko_cantelli P (fun i ω => ω i) hmeas hind hident
  filter_upwards [hGC] with ω hω
  rw [hmap 0] at hω
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hω
    (fun N => Real.sInf_nonneg (fun _ h => le_of_lt h.1)) (fun N => ?_)
  apply levy_le_sup _ _ (empCdf_mono _) (ProbabilityTheory.monotone_cdf _)
  intro x
  have hbdd : BddAbove (Set.range fun x : ℝ =>
      |(((Finset.range N).filter (fun i => ω i ≤ x)).card : ℝ) / N - cdf (F : Measure ℝ) x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h0 : 0 ≤ cdf (F : Measure ℝ) y := cdf_nonneg _ _
    have h1 : cdf (F : Measure ℝ) y ≤ 1 := cdf_le_one _ _
    have e0 : (0 : ℝ) ≤ (((Finset.range N).filter (fun i => ω i ≤ y)).card : ℝ) / N := by
      positivity
    have e1 : (((Finset.range N).filter (fun i => ω i ≤ y)).card : ℝ) / N ≤ 1 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · rw [div_le_one (by exact_mod_cast h)]
        have := Finset.card_filter_le (Finset.range N) (fun i => ω i ≤ y)
        simp only [Finset.card_range] at this
        exact_mod_cast this
    rw [abs_le]; constructor <;> linarith
  have := le_ciSup hbdd x
  unfold empCdf
  rw [card_sample_eq]
  exact this
