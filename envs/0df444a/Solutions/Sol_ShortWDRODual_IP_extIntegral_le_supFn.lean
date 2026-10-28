-- Prove2me | solution 1 for ShortWDRODual.IP.extIntegral_le_supFn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:19:23.184738+00:00
-- url     : https://prove2.me/submissions/2ad54e95-aed3-4061-a068-5a3fdb36957b

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

open ShortWDRODual.IP in
theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (φ : X × X → EReal) (hφ : Measurable φ) (hφtop : ∀ p, φ p ≠ ⊤)
    (hΦ : NullMeasurable (ShortWDRODual.Legendre.supFn φ) Phat) (γ : Measure (X × X)) (hγ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat) :
    extIntegral γ φ ≤ extIntegral Phat (ShortWDRODual.Legendre.supFn φ) := by
  set Φ := ShortWDRODual.Legendre.supFn φ with hΦdef
  have hle : ∀ p : X × X, φ p ≤ Φ p.1 := by
    intro p
    have : φ p = φ (p.1, p.2) := rfl
    rw [this]
    exact le_iSup (fun x => φ (p.1, x)) p.2
  have hmap : γ.map Prod.fst = Phat := hγ.2
  have hΦm : AEMeasurable Φ Phat := hΦ.aemeasurable
  have transfer : ∀ g : EReal → ℝ≥0∞, Measurable g →
      ∫⁻ p, g (Φ p.1) ∂γ = ∫⁻ xh, g (Φ xh) ∂Phat := by
    intro g hg
    have hf : AEMeasurable (fun xh => g (Φ xh)) (γ.map Prod.fst) := by
      rw [hmap]; exact hg.comp_aemeasurable hΦm
    rw [← lintegral_map' hf measurable_fst.aemeasurable, hmap]
  have hpos : ∫⁻ p, (φ p).toENNReal ∂γ ≤ ∫⁻ xh, (Φ xh).toENNReal ∂Phat := by
    rw [← transfer _ measurable_ereal_toENNReal]
    exact lintegral_mono (fun p => EReal.toENNReal_le_toENNReal (hle p))
  have hneg : ∫⁻ xh, (-Φ xh).toENNReal ∂Phat ≤ ∫⁻ p, (-φ p).toENNReal ∂γ := by
    rw [← transfer (fun e => (-e).toENNReal) (measurable_ereal_toENNReal.comp (continuous_neg (G := EReal)).measurable)]
    exact lintegral_mono (fun p => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hle p)))
  unfold extIntegral
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)
