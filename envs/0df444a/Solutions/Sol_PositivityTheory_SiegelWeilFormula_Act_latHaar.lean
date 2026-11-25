-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.latHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:30.410873+00:00
-- url     : https://prove2.me/submissions/a9b6f8e3-3224-4b9d-9cb6-ea17ccf7619f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act
namespace PositivityTheory.SiegelWeilFormula.Act
theorem _root_.solution : LatHaar := by
  unfold LatHaar
  intro V _ _ _ _ _ _ _ _ μ _ Γ _ φ hΓ s hs hs0 hstop
  have hmeas : Measurable φ := φ.continuous.measurable
  have : (μ.map φ).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨hmeas, fun t ht => ?_⟩
    rw [hc, Measure.smul_apply, ht, smul_zero]
  let e : Γ → Γ := fun g => ⟨φ.symm g, (hΓ _).1 (by simp)⟩
  have he : Function.Bijective e := by
    constructor
    · intro g g' h
      have h2 : φ (φ.symm (g : V)) = φ (φ.symm (g' : V)) := congrArg (fun x : Γ => φ (x : V)) h
      exact Subtype.ext (by simpa using h2)
    · intro g
      exact ⟨⟨φ g, (hΓ g).2 g.2⟩, Subtype.ext (by simp [e])⟩
  have hef : ∀ g : Γ, Function.Semiconj φ (e g +ᵥ ·) (g +ᵥ ·) := by
    intro g x
    show φ ((e g : V) + x) = (g : V) + φ x
    rw [map_add]
    simp [e]
  have hs' : IsAddFundamentalDomain Γ (φ ⁻¹' s) μ := hs.preimage_of_equiv hqmp he hef
  have heq : μ (φ ⁻¹' s) = μ s := hs'.measure_eq hs
  have hνs : (μ.map φ) s = μ s := by
    rw [← heq]
    exact (φ.toHomeomorph.toMeasurableEquiv).map_apply s
  rw [hc, Measure.coe_nnreal_smul_apply] at hνs
  have h1 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) = 1 := by
    have h3 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) * μ s = 1 * μ s := by
      rw [one_mul]
      exact hνs
    exact (ENNReal.mul_left_inj hs0 hstop).1 h3
  have h2 : Measure.addHaarScalarFactor (μ.map φ) μ = 1 := by exact_mod_cast h1
  rw [hc, h2, one_smul]
end PositivityTheory.SiegelWeilFormula.Act
