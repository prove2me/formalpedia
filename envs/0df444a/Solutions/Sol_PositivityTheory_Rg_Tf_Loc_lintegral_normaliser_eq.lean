-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.lintegral_normaliser_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:16.675828+00:00
-- url     : https://prove2.me/submissions/3864a16c-52ff-4f00-a401-a6eeb4ca2465

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]
variable [MeasurableSpace G]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫⁻ g, F g * ρ g ∂μG = ∫⁻ g, F g * ρ' g ∂μG := by
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd

  have e1 : ∫⁻ g, F g * ρ g ∂μG = ∫⁻ h, ∫⁻ g, F g * ρ g * ρ' ((h : G) * g) ∂μG ∂μH := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul, hρ'.2 g, mul_one]
      exact hρ'.1.comp (measurable_subtype_coe.mul_const g)
    · exact ((hF.comp measurable_snd).mul (hρ.1.comp measurable_snd)).mul
        (hρ'.1.comp hmulH) |>.aemeasurable

  have e2 : ∀ h : H, ∫⁻ g, F g * ρ g * ρ' ((h : G) * g) ∂μG =
      ∫⁻ g, F g * ρ' g * ρ (((h⁻¹ : H) : G) * g) ∂μG := by
    intro h
    rw [← lintegral_mul_left_eq_self _ ((h : G)⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [hFH _ (H.inv_mem h.2), mul_inv_cancel_left, Subgroup.coe_inv]
    ring

  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun h : H => ρ ((h : G) * g)), hρ.2 g, mul_one]
    exact hρ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const g)
  · have : Measurable fun p : G × H => ((p.2⁻¹ : H) : G) * p.1 :=
      (measurable_subtype_coe.comp (measurable_snd.inv)).mul measurable_fst
    exact ((hF.comp measurable_fst).mul (hρ'.1.comp measurable_fst)).mul
      (hρ.1.comp this) |>.aemeasurable
end PositivityTheory.Rg.Tf.Loc
