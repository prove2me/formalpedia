-- Prove2me | solution 1 for PrefRobustSR.WorstCase.equation_2_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:28:54.853484+00:00
-- url     : https://prove2.me/submissions/64cc4309-fa77-459d-8340-cd8c9600c9a7

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

set_option autoImplicit false
open MeasureTheory PrefRobustSR.WorstCase
open scoped ENNReal

namespace PRH

lemma subgrad (l : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ l) (hm : Monotone l) (a : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, l a + c * (x - a) ≤ l x := by
  have hint : a ∈ interior (Set.univ : Set ℝ) := by simp
  refine ⟨derivWithin l (Set.Ioi a) a, ?_, ?_⟩
  · have h1 := hc.leftDeriv_le_rightDeriv_of_mem_interior hint
    have h2 := hc.slope_le_leftDeriv_of_mem_interior (x := a - 1) (y := a) (Set.mem_univ _) hint
      (by linarith)
    have h3 : 0 ≤ slope l (a - 1) a := by
      rw [slope_def_field]
      have := hm (show a - 1 ≤ a by linarith)
      simp only [sub_sub_cancel]
      rw [div_one]; linarith
    linarith
  · intro x
    rcases lt_trichotomy x a with hx | hx | hx
    · have h1 := hc.leftDeriv_le_rightDeriv_of_mem_interior hint
      have h2 := hc.slope_le_leftDeriv_of_mem_interior (x := x) (y := a) (Set.mem_univ _) hint hx
      rw [slope_def_field] at h2
      have hax : 0 < a - x := by linarith
      rw [div_le_iff₀ hax] at h2
      have h3 : (l a - l x) ≤ derivWithin l (Set.Ioi a) a * (a - x) := by
        have := mul_le_mul_of_nonneg_right h1 hax.le
        linarith
      nlinarith
    · subst hx; simp
    · have h2 := hc.rightDeriv_le_slope_of_mem_interior (x := a) (y := x) hint (Set.mem_univ _) hx
      rw [slope_def_field] at h2
      have hax : 0 < x - a := by linarith
      rw [le_div_iff₀ hax] at h2
      linarith

end PRH

namespace PRH

open DupacovaWets.Consistency

lemma expect_coe_unfold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ) :
    expect P (fun ω => ((h ω : ℝ) : EReal)) =
      if ∫⁻ ω, ENNReal.ofReal (h ω) ∂P = ∞ then ⊤
      else ((∫⁻ ω, ENNReal.ofReal (h ω) ∂P : ℝ≥0∞) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-h ω) ∂P : ℝ≥0∞) : EReal) := by
  unfold expect
  simp only [EReal.real_coe_toENNReal]
  congr 4

lemma expect_real_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h B : Ω → ℝ) (hh : AEMeasurable h P) (hB : Integrable B P) (hle : ∀ ω, B ω ≤ h ω) :
    expect P (fun ω => ((h ω : ℝ) : EReal)) =
      ((∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P : ℝ≥0∞) : EReal) + ((∫ ω, B ω ∂P : ℝ) : EReal) := by
  rw [expect_coe_unfold]
  by_cases hU : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P = ∞
  · have h1 : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P = ∞ := by
      by_contra hne
      have hlt : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P < ∞ := lt_top_iff_ne_top.2 hne
      have h2 : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P ≤
          ∫⁻ ω, ENNReal.ofReal (h ω) ∂P + ∫⁻ ω, ENNReal.ofReal (-B ω) ∂P := by
        rw [← lintegral_add_left' hh.ennreal_ofReal]
        refine lintegral_mono fun ω => ?_
        calc ENNReal.ofReal (h ω - B ω) = ENNReal.ofReal (h ω + -B ω) := by rw [sub_eq_add_neg]
          _ ≤ _ := ENNReal.ofReal_add_le
      have h3 : ∫⁻ ω, ENNReal.ofReal (-B ω) ∂P < ∞ := hB.neg.lintegral_lt_top
      exact absurd hU (ne_of_lt (lt_of_le_of_lt h2 (ENNReal.add_lt_top.2 ⟨hlt, h3⟩)))
    rw [if_pos h1, hU]
    simp
  · have hU' : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P < ∞ := lt_top_iff_ne_top.2 hU
    have hnn : 0 ≤ᵐ[P] fun ω => h ω - B ω := Filter.Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply]; linarith [hle ω]
    have hint : Integrable (fun ω => h ω - B ω) P :=
      ⟨(hh.sub hB.aemeasurable).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal hnn).2 hU'⟩
    have hIh : Integrable h P := by
      have e : h = (fun ω => h ω - B ω) + B := by funext ω; simp
      rw [e]; exact hint.add hB
    have hp : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P ≠ ∞ := hIh.lintegral_lt_top.ne
    have hn : ∫⁻ ω, ENNReal.ofReal (-h ω) ∂P ≠ ∞ := hIh.neg.lintegral_lt_top.ne
    rw [if_neg hp]
    have e1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIh
    have e2 : ENNReal.ofReal (∫ ω, (h ω - B ω) ∂P) = ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hint hnn
    have e3 : (∫ ω, h ω ∂P) = (∫ ω, (h ω - B ω) ∂P) + ∫ ω, B ω ∂P := by
      rw [← integral_add hint hB]; simp
    have e4 : 0 ≤ ∫ ω, (h ω - B ω) ∂P := integral_nonneg_of_ae hnn
    rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_ennreal_toReal hU, ← e2, ENNReal.toReal_ofReal e4, ← EReal.coe_sub,
      ← EReal.coe_add]
    congr 1
    linarith

end PRH

namespace PRH

open DupacovaWets.Consistency

variable {Ω : Type*} [MeasurableSpace Ω]

lemma loss_cont (l : ℝ → ℝ) (hl : l ∈ LossClass) : Continuous l := by
  have := hl.1.continuousOn isOpen_univ
  exact continuousOn_univ.1 this

lemma loss_meas (P : Measure Ω) (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    AEMeasurable (fun ω => l (-Z ω - t)) P := by
  have h1 : AEStronglyMeasurable (fun ω => -Z ω - t) P :=
    hZ.aestronglyMeasurable.neg.sub aestronglyMeasurable_const
  exact ((loss_cont l hl).comp_aestronglyMeasurable h1).aemeasurable

lemma jensen (P : Measure Ω) [IsProbabilityMeasure P] (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    ((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) ≤
      expect P (fun ω => ((l (-Z ω - t) : ℝ) : EReal)) := by
  obtain ⟨c, hc0, hc⟩ := subgrad l hl.1 hl.2.1 (-(∫ ω, Z ω ∂P) - t)
  set a := -(∫ ω, Z ω ∂P) - t with ha
  set B : Ω → ℝ := fun ω => (l a - c * t - c * a) + (-c) * Z ω with hB
  have hBi : Integrable B P := (integrable_const _).add (hZ.const_mul _)
  have hBint : ∫ ω, B ω ∂P = l a := by
    simp only [hB]
    rw [integral_add (integrable_const _) (hZ.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    have : (∫ ω, Z ω ∂P) = -a - t := by simp [ha]
    rw [this]; ring
  have hBle : ∀ ω, B ω ≤ l (-Z ω - t) := fun ω => by
    have := hc (-Z ω - t)
    simp only [hB]; nlinarith
  rw [expect_real_eq P _ B (loss_meas P l hl Z hZ t) hBi hBle, hBint]
  exact le_add_of_nonneg_left (by positivity)

end PRH

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    (⨆ l ∈ L, (((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) -
      ((l 0 : ℝ) : EReal))) ≤
      ⨆ l ∈ L, gap P l Z t := by
  refine iSup₂_mono fun l hl => ?_
  exact EReal.sub_le_sub (PRH.jensen P l (hL hl) Z hZ t) le_rfl

