-- Prove2me | solution 1 for ShortWDRODual.Tight.integral_le_supFn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:47:08.387199+00:00
-- url     : https://prove2.me/submissions/59036f9d-16a6-4a01-a9bc-41587bae0563

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality

theorem wdro3_supFn_measurable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → ℝ) (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) :
    Measurable (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by
  have hlsc : LowerSemicontinuous (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by
    unfold ShortWDRODual.Legendre.supFn pWassIntegrand
    refine lowerSemicontinuous_iSup fun x => ?_
    have hc : Continuous fun xh : X => ((f x - lam * dist xh x ^ p : ℝ) : EReal) := by
      refine continuous_coe_real_ereal.comp ?_
      refine continuous_const.sub (continuous_const.mul ?_)
      exact (continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr (by linarith))
    exact hc.lowerSemicontinuous
  exact hlsc.measurable

end ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Tight

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat,
      extIntegral γ (pWassIntegrand f lam p) ≤ extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by
  intro γ hγ
  obtain ⟨_, hmap⟩ := hγ
  set Φ := ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p) with hΦ
  have hΦm : Measurable Φ := wdro3_supFn_measurable f p hp lam
  have hle : ∀ q : X × X, pWassIntegrand f lam p q ≤ Φ q.1 := by
    intro q
    show pWassIntegrand f lam p q ≤ ⨆ x, pWassIntegrand f lam p (q.1, x)
    exact le_iSup (fun x => pWassIntegrand f lam p (q.1, x)) q.2
  have hA : ∫⁻ q, (pWassIntegrand f lam p q).toENNReal ∂γ ≤ ∫⁻ x, (Φ x).toENNReal ∂Phat := by
    calc ∫⁻ q, (pWassIntegrand f lam p q).toENNReal ∂γ
        ≤ ∫⁻ q, (Φ q.1).toENNReal ∂γ := lintegral_mono fun q => EReal.toENNReal_le_toENNReal (hle q)
      _ = ∫⁻ x, (Φ x).toENNReal ∂(γ.map Prod.fst) :=
          (lintegral_map hΦm.ereal_toENNReal measurable_fst).symm
      _ = ∫⁻ x, (Φ x).toENNReal ∂Phat := by rw [hmap]
  have hB : ∫⁻ x, (-Φ x).toENNReal ∂Phat ≤ ∫⁻ q, (-pWassIntegrand f lam p q).toENNReal ∂γ := by
    calc ∫⁻ x, (-Φ x).toENNReal ∂Phat
        = ∫⁻ x, (-Φ x).toENNReal ∂(γ.map Prod.fst) := by rw [hmap]
      _ = ∫⁻ q, (-Φ q.1).toENNReal ∂γ :=
          lintegral_map hΦm.neg.ereal_toENNReal measurable_fst
      _ ≤ ∫⁻ q, (-pWassIntegrand f lam p q).toENNReal ∂γ :=
          lintegral_mono fun q => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hle q))
  unfold extIntegral
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hA)
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hB)

