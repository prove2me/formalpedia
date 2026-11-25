-- Prove2me | solution 1 for PI.QuotMeasUniqW.wqUnique_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:43.985774+00:00
-- url     : https://prove2.me/submissions/b55f7084-f0a2-403f-903e-31aabffd4265

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_WqUniqueOf

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
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution (hw : QmuWeight) (hl : QmuLift) : PI.WeilQuotMeas.WqUnique := by
  unfold PI.WeilQuotMeas.WqUnique
  intro G _ _ _ _ _ _ _ _ H hH ρ ρ' hρ hK hinv hK' hinv'
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure H, ν = Measure.haar := ⟨_, rfl⟩
  have hν : ν.IsHaarMeasure := by rw [hνdef]; infer_instance
  haveI := hν
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨w, hwm, hwW⟩ := hw G H hH ν hν
  obtain ⟨l, hlI, hlF, hlW⟩ := hl G H hH ν hν ρ hK hinv
  obtain ⟨l', hlI', hlF', hlW'⟩ := hl G H hH ν hν ρ' hK' hinv'

  obtain ⟨W, hW⟩ : ∃ W : G → ℝ≥0∞, ∀ g, W g = ∫⁻ h : H, w (g * h) ∂ν := ⟨_, fun _ => rfl⟩
  have hW0 : ∀ g, W g ≠ 0 := fun g => by rw [hW]; exact (hwW g).1
  have hWt : ∀ g, W g ≠ ∞ := fun g => by rw [hW]; exact (hwW g).2
  have hWmul : ∀ (g : G) (h₀ : H), W (g * h₀) = W g := by
    intro g h₀
    rw [hW, hW]
    have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => w (g * h)) h₀
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hwc : ∀ g : G, Measurable fun h : H => w (g * h) :=
    fun g => hwm.comp (measurable_const.mul measurable_subtype_coe)
  have hWm : Measurable W := by
    have e : W = fun g => ∫⁻ h : H, w (g * h) ∂ν := funext hW
    rw [e]
    exact (hwm.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'

  obtain ⟨f, hf⟩ : ∃ f : Set (G ⧸ H) → G → ℝ≥0∞, ∀ s x,
      f s x = s.indicator 1 (QuotientGroup.mk x : G ⧸ H) * (w x * (W x)⁻¹) := ⟨_, fun _ _ => rfl⟩
  have hfm : ∀ s, MeasurableSet s → Measurable (f s) := by
    intro s hs
    have e : f s = fun x => s.indicator 1 (QuotientGroup.mk x : G ⧸ H) * (w x * (W x)⁻¹) :=
      funext (hf s)
    rw [e]
    exact ((measurable_const.indicator hs).comp
      (measurable_quotient_mk'' : Measurable (QuotientGroup.mk : G → G ⧸ H))).mul (hwm.mul hWm.inv)
  have hrec : ∀ (μ : Measure (G ⧸ H)) (m : Measure G),
      (∀ φ : G → ℝ≥0∞, Measurable φ →
        ∫⁻ x, φ x ∂m = ∫⁻ y : G ⧸ H, ∫⁻ h : H, φ (@Quotient.out G (QuotientGroup.leftRel H) y * h) ∂ν ∂μ) →
      ∀ s, MeasurableSet s → μ s = ∫⁻ x, f s x ∂m := by
    intro μ m hm s hs
    rw [hm _ (hfm s hs), ← lintegral_indicator_one hs]
    refine lintegral_congr (fun y => ?_)
    have hy : ∀ h : H, (QuotientGroup.mk (@Quotient.out G (QuotientGroup.leftRel H) y * (h : G)) : G ⧸ H) = y := by
      intro h
      rw [QuotientGroup.mk_mul_of_mem _ h.2]
      exact @Quotient.out_eq G (QuotientGroup.leftRel H) y
    simp only [hf, hy, hWmul]
    rw [lintegral_const_mul _ ((hwc _).mul_const _), lintegral_mul_const _ (hwc _), ← hW,
      ENNReal.mul_inv_cancel (hW0 _) (hWt _), mul_one]

  haveI := hlI; haveI := hlF; haveI := hlI'; haveI := hlF'
  obtain ⟨μG, hμG⟩ : ∃ μG : Measure G, μG = Measure.haar := ⟨_, rfl⟩
  haveI : μG.IsHaarMeasure := by rw [hμG]; infer_instance
  obtain ⟨c, hc1⟩ : ∃ c : NNReal, l = c • μG := ⟨_, Measure.isMulLeftInvariant_eq_smul l μG⟩
  obtain ⟨c', hc2⟩ : ∃ c' : NNReal, l' = c' • μG := ⟨_, Measure.isMulLeftInvariant_eq_smul l' μG⟩
  have e1 : ∀ s, MeasurableSet s → ρ s = (c : ℝ≥0∞) * ∫⁻ x, f s x ∂μG := fun s hs => by
    rw [hrec ρ l hlW s hs, hc1, lintegral_smul_measure]
    rfl
  have e2 : ∀ s, MeasurableSet s → ρ' s = (c' : ℝ≥0∞) * ∫⁻ x, f s x ∂μG := fun s hs => by
    rw [hrec ρ' l' hlW' s hs, hc2, lintegral_smul_measure]
    rfl
  have hc : c ≠ 0 := by
    intro h0
    apply hρ
    refine Measure.ext fun s hs => ?_
    rw [e1 s hs, h0]
    simp
  refine ⟨((c' / c : NNReal) : ℝ≥0∞), Measure.ext fun s hs => ?_⟩
  rw [Measure.smul_apply, e1 s hs, e2 s hs, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    div_mul_cancel₀ _ hc]
end PI.QuotMeasUniqW
