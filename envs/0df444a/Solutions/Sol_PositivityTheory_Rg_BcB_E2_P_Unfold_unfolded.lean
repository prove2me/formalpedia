-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Unfold.unfolded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:10.544886+00:00
-- url     : https://prove2.me/submissions/64b703ad-b49e-41c2-b1dd-9683377f2142

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Unfold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Unfold
namespace PositivityTheory.Rg.BcB.E2.P.Unfold
theorem _root_.solution (hk : KerBasic) (X : Ctx) (φ u : X.G → ℂ) (hφ : Tst φ) (hu : Continuous u)
    (hinv : ∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) (x : X.G) :
    ∫ y, ker X.Γ φ x y * u y ∂X.ν = ∫ y, φ y * u (x * y) ∂X.μ := by
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * u z with hg
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hu
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * u z = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * u z := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, hinv γ γ.2 z, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ⊤ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  refine (X.fd.integral_eq_tsum'' g hgi).symm.trans ?_
  rw [← integral_mul_left_eq_self g x]
  simp [hg]
end PositivityTheory.Rg.BcB.E2.P.Unfold
