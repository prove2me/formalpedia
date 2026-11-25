-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:31.549551+00:00
-- url     : https://prove2.me/submissions/7b9eec78-54e5-45fb-ba75-f94e972ceb7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (q : ℕ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    (v0 : EuclideanSpace ℂ ι) (ρ K : ℝ)
    (hK : ∀ S : Finset (EuclideanSpace ℂ ι), (∀ a ∈ S, ‖a‖ ≤ ρ) →
      (∀ a ∈ S, ∀ b ∈ S, a - b ∈ lat Y.b) → (S.card : ℝ) ≤ K) :
    ∫ u in closedBall v0 ρ, Y.ptN2 q F u ≤
      K * ∫ u in ZSpan.fundamentalDomain Y.b, Y.ptN2 q F u := by
  classical
  have hc : Continuous F := hF.1.continuous
  have hfc : Continuous fun u => Y.ptN2 q F u := by
    unfold GT.ptN2
    exact (hc.norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hf0 : ∀ u, 0 ≤ Y.ptN2 q F u := fun u => by
    unfold GT.ptN2
    positivity
  have hmeas : Measurable fun u => ENNReal.ofReal (Y.ptN2 q F u) :=
    ENNReal.measurable_ofReal.comp hfc.measurable
  have hfd : MeasureTheory.IsAddFundamentalDomain (lat Y.b) (ZSpan.fundamentalDomain Y.b)
      MeasureTheory.volume := ZSpan.isAddFundamentalDomain Y.b MeasureTheory.volume
  have hK0 : 0 ≤ K := by
    have h := hK ∅ (by simp) (by simp)
    simpa using h
  have hcount : ∀ x : EuclideanSpace ℂ ι, ∑' γ : lat Y.b,
      (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ x) ≤ ENNReal.ofReal K := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun T => ?_
    have h1 : ∑ γ ∈ T, (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ x) =
        ((T.filter (fun γ : lat Y.b => γ +ᵥ x ∈ closedBall v0 ρ)).card : ENNReal) := by
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      by_cases h : γ +ᵥ x ∈ closedBall v0 ρ
      · rw [Set.indicator_of_mem h, if_pos h]
      · rw [Set.indicator_of_notMem h, if_neg h]
    rw [h1]
    have hinj : Function.Injective (fun γ : lat Y.b => (γ +ᵥ x) - v0) := by
      intro a b h
      exact Subtype.ext (by simpa [Submodule.vadd_def, vadd_eq_add] using h)
    have hS := hK ((T.filter (fun γ : lat Y.b => γ +ᵥ x ∈ closedBall v0 ρ)).image
        (fun γ : lat Y.b => (γ +ᵥ x) - v0)) ?_ ?_
    · rw [Finset.card_image_of_injective _ hinj] at hS
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hS
    · intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      have hγ' := (Finset.mem_filter.1 hγ).2
      rw [Metric.mem_closedBall, dist_eq_norm] at hγ'
      exact hγ'
    · intro a ha b hb
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨γ', _, rfl⟩ := Finset.mem_image.1 hb
      have e : ((γ +ᵥ x) - v0) - ((γ' +ᵥ x) - v0) = (γ : EuclideanSpace ℂ ι) - γ' := by
        simp only [Submodule.vadd_def, vadd_eq_add]
        abel
      rw [e]
      exact sub_mem γ.2 γ'.2
  have hper : ∀ (γ : lat Y.b) (u : EuclideanSpace ℂ ι),
      (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) (γ +ᵥ u) =
        (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) * ENNReal.ofReal (Y.ptN2 q F u) := by
    intro γ u
    have hp : Y.ptN2 q F (γ +ᵥ u) = Y.ptN2 q F u := by
      rw [Submodule.vadd_def, vadd_eq_add]
      exact lemS_periodic Y q hF γ.2 u
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hp, one_mul]
    · rw [zero_mul]
  have hae : ∀ γ : lat Y.b, AEMeasurable (fun u => (closedBall v0 ρ).indicator
      (fun _ => (1 : ENNReal)) (γ +ᵥ u) * ENNReal.ofReal (Y.ptN2 q F u))
      (MeasureTheory.volume.restrict (ZSpan.fundamentalDomain Y.b)) := fun γ =>
    (((measurable_const.indicator measurableSet_closedBall).comp (measurable_const_vadd γ)).mul
      hmeas).aemeasurable
  haveI : MeasureTheory.VAddInvariantMeasure (lat Y.b) (EuclideanSpace ℂ ι) MeasureTheory.volume :=
    ⟨fun c s _ => MeasureTheory.measure_preimage_add _ (c : EuclideanSpace ℂ ι) s⟩
  have hlin : ∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u) ≤
      ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) := by
    calc ∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u)
        = ∫⁻ u, (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) u :=
          (MeasureTheory.lintegral_indicator measurableSet_closedBall _).symm
      _ = ∑' γ : lat Y.b, ∫⁻ u in ZSpan.fundamentalDomain Y.b,
            (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) (γ +ᵥ u) :=
          hfd.lintegral_eq_tsum'' _
      _ = ∑' γ : lat Y.b, ∫⁻ u in ZSpan.fundamentalDomain Y.b,
            (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) *
              ENNReal.ofReal (Y.ptN2 q F u) :=
          tsum_congr fun γ => MeasureTheory.lintegral_congr fun u => hper γ u
      _ = ∫⁻ u in ZSpan.fundamentalDomain Y.b, ∑' γ : lat Y.b,
            (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) *
              ENNReal.ofReal (Y.ptN2 q F u) :=
          (MeasureTheory.lintegral_tsum hae).symm
      _ ≤ ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal K * ENNReal.ofReal (Y.ptN2 q F u) := by
          refine MeasureTheory.lintegral_mono fun u => ?_
          rw [ENNReal.tsum_mul_right]
          exact mul_le_mul_of_nonneg_right (hcount u) zero_le
      _ = ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hint_D : MeasureTheory.IntegrableOn (fun u => Y.ptN2 q F u) (ZSpan.fundamentalDomain Y.b) :=
    (hfc.continuousOn.integrableOn_compact
      (ZSpan.fundamentalDomain_isBounded Y.b).isCompact_closure).mono_set subset_closure
  have hfin : ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) ≠ ⊤ :=
    (MeasureTheory.Integrable.lintegral_lt_top hint_D).ne
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => hf0 u)
      hfc.aestronglyMeasurable,
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => hf0 u)
      hfc.aestronglyMeasurable]
  calc (∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u)).toReal
      ≤ (ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlin
    _ = K * (∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
end ReciprocityTheory.ChartRestriction.G.I2
