-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.lintegral_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:01:50.752802+00:00
-- url     : https://prove2.me/submissions/e5987beb-6052-4dfe-893c-8f74cace88d0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
import Theorems.Thm_PositivityTheory_ThKR_Sieg_isClosed_image_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}
namespace PositivityTheory.ThKR.Sieg
theorem _root_.solution (ν : Measure G) [ν.IsHaarMeasure] (τ : G → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → G) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, ν.map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • ν) {Ω : Set G} (hΩ : IsCompact Ω)
    (hΩτ : ∀ p ∈ Ω, τ p = 0) :
    ∃ C : ℝ≥0, ∀ h : (Fin r → ℝ) → ℝ≥0∞, Measurable h →
      ∫⁻ p in Ω * range a, h (τ p) ∂ν = C * ∫⁻ t, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hT : IsClosed (Ω * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ
  set T := Ω * range a with hTdef
  let w : G → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (ρ (τ p)))
  have hw : Measurable w := (Real.continuous_exp.comp (hρ.comp hτ)).measurable.ennreal_ofReal
  let m : Measure (Fin r → ℝ) := ((ν.restrict T).withDensity w).map τ
  have hm : ∀ g : (Fin r → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ t, g t ∂m = ∫⁻ p, T.indicator (fun p => w p * g (τ p)) p ∂ν :=
    fun g hg => by
      rw [lintegral_map hg hτ.measurable, lintegral_withDensity_eq_lintegral_mul _ hw (g := fun p => g (τ p)) (hg.comp hτ.measurable),
        lintegral_indicator hT.measurableSet]
      rfl
  have hTa : ∀ s p, p * a s ∈ T ↔ p ∈ T := by
    have : ∀ s p, p ∈ T → p * a s ∈ T := by
      rintro s _ ⟨p, hp, _, ⟨t, rfl⟩, rfl⟩
      exact ⟨p, hp, _, ⟨t + s, rfl⟩, by simp [hadd, mul_assoc]⟩
    have h0 : a 0 = 1 := by simpa using hadd 0 0
    refine fun s p => ⟨fun h => ?_, this s p⟩
    have := this (-s) _ h
    rwa [mul_assoc, ← hadd, add_neg_cancel, h0, mul_one] at this
  have : IsAddLeftInvariant m := ⟨fun s => by
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [lintegral_map hg (measurable_const_add s), hm (fun t => g (s + t)) (hg.comp (measurable_const_add s)), hm _ hg]
    have hG : Measurable (T.indicator fun p => w p * g (τ p)) :=
      (hw.mul (hg.comp hτ.measurable)).indicator hT.measurableSet
    have e := lintegral_map (μ := ν) hG (measurable_mul_const (a s))
    rw [hmod, lintegral_smul_measure, smul_eq_mul] at e
    have h0 : ENNReal.ofReal (Real.exp (ρ s)) ≠ 0 := by simp [Real.exp_pos]
    rw [← ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top, e, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp, indicator_of_mem ((hTa s p).2 hp)]
      simp only [w, hτm, hτa, hρa, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, add_comm s]
      ring
    · rw [indicator_of_notMem hp, indicator_of_notMem (mt (hTa s p).1 hp), mul_zero]⟩
  have : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    obtain ⟨B, hB⟩ := hC.bddAbove_image hρ.continuousOn
    rw [← lintegral_indicator_one hC.measurableSet, hm _ (measurable_one.indicator hC.measurableSet)]
    have hK : IsCompact (Ω * a '' C) := hΩ.mul (hC.image ha)
    refine lt_of_le_of_lt (lintegral_mono (g := (Ω * a '' C).indicator fun _ => ENNReal.ofReal (Real.exp B)) fun p => ?_) ?_
    · by_cases hp : p ∈ T
      · by_cases hp' : τ p ∈ C
        · obtain ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩ := hp
          have e : τ (q * a t) = t := by rw [hτm, hτa, hΩτ q hq, zero_add]
          simp only [e] at hp'
          rw [indicator_of_mem (show q * a t ∈ T from ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩),
            indicator_of_mem (show q * a t ∈ Ω * a '' C from ⟨q, hq, _, ⟨t, hp', rfl⟩, rfl⟩), e, indicator_of_mem hp']
          simp only [w, e, Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hB ⟨t, hp', rfl⟩))
        · rw [indicator_of_mem hp, indicator_of_notMem hp', mul_zero]
          exact zero_le
      · rw [indicator_of_notMem hp]
        exact zero_le
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  refine ⟨addHaarScalarFactor m volume, fun h hh => ?_⟩
  have hg : Measurable fun t => h t * ENNReal.ofReal (Real.exp (-ρ t)) :=
    hh.mul (Real.continuous_exp.comp hρ.neg).measurable.ennreal_ofReal
  have e := hm _ hg
  rw [isAddLeftInvariant_eq_smul m volume, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    lintegral_indicator hT.measurableSet] at e
  rw [e]
  refine lintegral_congr fun p => ?_
  rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel]
  simp
end PositivityTheory.ThKR.Sieg
