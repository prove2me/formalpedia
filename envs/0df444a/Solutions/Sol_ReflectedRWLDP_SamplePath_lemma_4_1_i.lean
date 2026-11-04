-- Prove2me | solution 1 for ReflectedRWLDP.SamplePath.lemma_4_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:46:28.246193+00:00
-- url     : https://prove2.me/submissions/76ee0375-9344-4b1c-86e0-65ab05f24f4d

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath.L41i

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Jensen: `Λ*(E V) = 0`. -/
lemma lambdaStar_mean (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ)
    (hV : Integrable V P) : LambdaStar P V (∫ ω, V ω ∂P) = 0 := by
  unfold LambdaStar
  apply EReal.toENNReal_of_nonpos
  unfold BellWilliams2001.ThresholdPolicy.legendre BellWilliams2001.ThresholdPolicy.logMGF
  refine iSup_le fun l => ?_
  set μ := ∫ ω, V ω ∂P with hμ
  have key : ENNReal.ofReal (Real.exp (l * μ)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * V ω)) ∂P := by
    by_cases hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * V ω)) ∂P = ⊤
    · rw [hfin]; exact le_top
    · have hmeas : AEStronglyMeasurable (fun ω => Real.exp (l * V ω)) P :=
        Real.continuous_exp.comp_aestronglyMeasurable (hV.aestronglyMeasurable.const_mul l)
      have hint : Integrable (fun ω => Real.exp (l * V ω)) P := by
        refine ⟨hmeas, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => (Real.exp_pos _).le)]
        exact lt_top_iff_ne_top.mpr hfin
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun ω => (Real.exp_pos _).le)]
      apply ENNReal.ofReal_le_ofReal
      have h1 : ∀ ω, Real.exp (l * μ) * (1 + (l * V ω - l * μ)) ≤ Real.exp (l * V ω) := by
        intro ω
        have := Real.add_one_le_exp (l * V ω - l * μ)
        have h2 : Real.exp (l * V ω) = Real.exp (l * μ) * Real.exp (l * V ω - l * μ) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      have hint1 : Integrable (fun ω => 1 + (l * V ω - l * μ)) P :=
        (integrable_const 1).add ((hV.const_mul l).sub (integrable_const _))
      have hint2 : Integrable (fun ω => Real.exp (l * μ) * (1 + (l * V ω - l * μ))) P :=
        hint1.const_mul _
      calc Real.exp (l * μ) = ∫ ω, Real.exp (l * μ) * (1 + (l * V ω - l * μ)) ∂P := by
            have hA : Integrable (fun ω => l * V ω) P := hV.const_mul l
            have hB : Integrable (fun ω => l * V ω - l * μ) P := hA.sub (integrable_const _)
            have hC : ∫ ω, (1 + (l * V ω - l * μ)) ∂P = 1 := by
              rw [integral_add (integrable_const 1) hB, integral_sub hA (integrable_const _),
                integral_const_mul]
              simp [← hμ]
            rw [integral_const_mul, hC, mul_one]
        _ ≤ _ := integral_mono hint2 hint h1
  have hlog : ((l * μ : ℝ) : EReal) ≤
      ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (l * V ω)) ∂P) := by
    calc ((l * μ : ℝ) : EReal) = ENNReal.log (ENNReal.ofReal (Real.exp (l * μ))) := by
          rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
      _ ≤ _ := ENNReal.log_monotone key
  exact EReal.sub_nonpos.mpr hlog

theorem main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ y : ℝ, ybar P U p ≤ y →
      (∃ ξ ∈ BsetAC p y, rateI P U y ξ = 0) ∧ Bstar P U p y = 0 := by
  intro y hy
  have := h.isProbability
  set μ := ∫ ω, U 0 ω ∂P with hμ
  have hμneg : μ < 0 := h.mean_neg
  set c := -μ with hc
  have hcpos : 0 < c := by linarith
  have hp := h.p_pos
  have hp1 : 0 < p + 1 := by linarith
  -- `ȳ > 0`, hence `y > 0`
  have hybar_pos : 0 < ybar P U p := by
    unfold ybar
    apply Real.rpow_pos_of_pos
    rw [← hμ, abs_of_neg hμneg]
    exact mul_pos (by linarith) hp1
  have hypos : 0 < y := lt_of_lt_of_le hybar_pos hy
  -- `c (p+1) ≤ y^(p+1)`
  have hyp1 : c * (p + 1) ≤ y ^ (p + 1) := by
    have h0 : 0 ≤ c * (p + 1) := (mul_pos hcpos hp1).le
    have hy' : (c * (p + 1)) ^ ((p + 1)⁻¹) ≤ y := by
      have : ybar P U p = (c * (p + 1)) ^ ((p + 1)⁻¹) := by
        unfold ybar alpha
        rw [← hμ, abs_of_neg hμneg, one_div, add_comm 1 p]
      rw [← this]; exact hy
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hy' hp1.le
    rwa [Real.rpow_inv_rpow h0 hp1.ne'] at this
  -- the path
  set ξ : ℝ → ℝ := fun t => y + μ * t with hξ
  have hξcont : Continuous ξ := by
    simp only [hξ]; fun_prop
  have hξ0 : ξ 0 = y := by simp [hξ]
  have hBV : IsBVFrom0 ξ := by
    refine ⟨fun t _ => hξcont.continuousAt.continuousWithinAt,
      fun t _ => ⟨ξ t, hξcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩,
      fun t ht => ?_⟩
    have hL : LipschitzWith (Real.toNNReal |μ|) ξ := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp only [hξ, Real.dist_eq]
      rw [Real.coe_toNNReal _ (abs_nonneg _)]
      rw [show y + μ * a - (y + μ * b) = μ * (a - b) by ring, abs_mul]
    have := (hL.lipschitzOnWith (s := Icc 0 t)).locallyBoundedVariationOn
    have h2 := this 0 t ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩
    simpa [Set.inter_self] using h2
  have hrep : IsLebRep (Ici 0) ξ (fun _ => μ) 0 0 := by
    refine ⟨fun t _ => integrableOn_const (by simp), fun t _ => rfl, fun t _ => rfl,
      ?_, ?_, fun t _ => ?_⟩
    · rw [StieltjesFunction.measure_zero]; exact MeasureTheory.Measure.MutuallySingular.zero_left
    · rw [StieltjesFunction.measure_zero]; exact MeasureTheory.Measure.MutuallySingular.zero_left
    · show y + μ * t = y + μ * 0 + (∫ _ in (0 : ℝ)..t, μ) + (0 : StieltjesFunction ℝ) t -
        (0 : StieltjesFunction ℝ) t
      rw [intervalIntegral.integral_const]
      simp [mul_comm]
  have hcost : cost P U (exitTime ξ) (fun _ => μ) 0 0 = 0 := by
    unfold cost
    have hL : LambdaStar P (U 0) μ = 0 := lambdaStar_mean P (U 0) h.integrable
    have hup : upTo (0 : StieltjesFunction ℝ) (exitTime ξ) = 0 := by
      unfold upTo
      simp
    simp [hL, hup]
  have hrate : rateI P U y ξ = 0 := by
    unfold rateI
    rw [if_pos ⟨hξ0, hBV⟩]
    refine le_antisymm ?_ bot_le
    rw [← hcost]
    exact iInf_le_of_le _ (iInf_le_of_le 0 (iInf_le_of_le 0 (iInf_le_of_le hrep le_rfl)))
  -- the area
  set a := y / c with ha
  have hapos : 0 < a := div_pos hypos hcpos
  have hξpos : ∀ s, s < a → 0 < ξ s := by
    intro s hs
    simp only [hξ]
    have : c * s < y := by rw [ha, lt_div_iff₀ hcpos] at hs; linarith
    linarith
  have hrefl : ∀ s, 0 ≤ s → s < a → reflect ξ s = ξ s := by
    intro s hs0 hs
    unfold reflect
    haveI : Nonempty (Icc (0 : ℝ) s) := ⟨⟨0, le_rfl, hs0⟩⟩
    have : ∀ r : Icc (0 : ℝ) s, min (ξ r) 0 = 0 := fun r =>
      min_eq_right (hξpos r (lt_of_le_of_lt r.2.2 hs)).le
    simp only [this, ciInf_const, sub_zero]
  have hexit : ENNReal.ofReal a ≤ exitTime ξ := by
    unfold exitTime
    refine le_iInf fun t => le_iInf fun ht => le_iInf fun hrt => ?_
    by_contra hlt
    push Not at hlt
    have hta : t < a := by
      rwa [ENNReal.ofReal_lt_ofReal_iff hapos] at hlt
    rw [hrefl t ht.le hta] at hrt
    exact (hξpos t hta).ne' hrt
  have hsub : Ioo 0 a ⊆ window (exitTime ξ) := fun s hs =>
    ⟨hs.1, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hapos).mpr hs.2) hexit⟩
  have hint_val : ∫ s in (0 : ℝ)..a, (y - c * s) ^ p = c⁻¹ * (y ^ (p + 1) / (p + 1)) := by
    rw [intervalIntegral.integral_comp_sub_mul (fun x => x ^ p) hcpos.ne' y]
    rw [integral_rpow (Or.inl (by linarith))]
    have : y - c * a = 0 := by rw [ha]; field_simp; ring
    rw [this, Real.zero_rpow hp1.ne', sub_zero, smul_eq_mul, mul_zero, sub_zero]
  have hcont : Continuous fun s : ℝ => (y - c * s) ^ p :=
    (continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
      (fun _ => Or.inr hp.le)
  have harea : 1 ≤ areaToExit p ξ := by
    unfold areaToExit
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (c⁻¹ * (y ^ (p + 1) / (p + 1))) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_div_assoc, le_div_iff₀ hp1, inv_mul_eq_div, le_div_iff₀ hcpos]
          linarith
      _ = ∫⁻ s in Ioo 0 a, ENNReal.ofReal ((y - c * s) ^ p) := by
          rw [← hint_val, intervalIntegral.integral_of_le hapos.le]
          rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := a))]
          · rw [ofReal_integral_eq_lintegral_ofReal]
            · exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
              apply Real.rpow_nonneg
              have : c * s ≤ c * a := mul_le_mul_of_nonneg_left hs.2 hcpos.le
              have : c * a = y := by rw [ha]; field_simp
              linarith
      _ = ∫⁻ s in Ioo 0 a, ENNReal.ofReal (reflect ξ s ^ p) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
          rw [hrefl s hs.1.le hs.2]
          simp only [hξ, hc]
          ring_nf
      _ ≤ _ := lintegral_mono_set hsub
  have hmem : ξ ∈ BsetAC p y :=
    ⟨⟨hBV, hξ0, harea⟩, ⟨fun _ => μ, fun t _ => integrableOn_const (by simp), fun t _ => by
      rw [intervalIntegral.integral_const]; simp [hξ, mul_comm]⟩⟩
  refine ⟨⟨ξ, hmem, hrate⟩, le_antisymm ?_ bot_le⟩
  unfold Bstar
  rw [← hrate]
  exact iInf₂_le ξ hmem.1

end ReflectedRWLDP.SamplePath.L41i

open ReflectedRWLDP.SamplePath in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ y : ℝ, ybar P U p ≤ y →
      (∃ ξ ∈ BsetAC p y, rateI P U y ξ = 0) ∧ Bstar P U p y = 0 :=
  ReflectedRWLDP.SamplePath.L41i.main P U p h
