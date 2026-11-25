-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.subMeanValuePolydisc_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:49.455804+00:00
-- url     : https://prove2.me/submissions/6a10ecd0-9dc7-4af6-bf31-50b747ffdb29

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_smul_mp
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_measurable_piecewise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshMean
theorem _root_.solution : SubMeanPolydiscStatement := by
  intro D U φ z t hU hφ ht hK
  set K := closedBall z t with hKdef
  have hKc : IsCompact K := isCompact_closedBall z t
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hzK : z ∈ K := mem_closedBall_self ht.le
  obtain ⟨x0, -, hx0⟩ := (hφ.1.mono hK).exists_isMaxOn ⟨z, hzK⟩ hKc
  set M := φ x0 with hMdef
  have hM : ∀ x ∈ K, φ x ≤ M := fun x hx => hx0 hx
  set φU := U.indicator φ with hφUdef
  have hφUm : Measurable φU := measurable_piecewise hU hφ.1
  have hφU : ∀ x ∈ K, φU x = φ x := fun x hx => Set.indicator_of_mem (hK hx) φ
  set Φ : (Fin D → ℂ) → ENNReal := fun x => ENNReal.ofReal (M - φU x) with hΦdef
  have hΦm : Measurable Φ := ENNReal.measurable_ofReal.comp (measurable_const.sub hφUm)
  set k : (Fin D → ℂ) → ENNReal := fun v => K.indicator Φ (z + v) with hkdef
  have hkm : Measurable k := (hΦm.indicator hKm).comp (measurable_const_add z)
  have hk : ∫⁻ v, k v = ∫⁻ x in K, Φ x := by
    rw [lintegral_add_left_eq_self (fun x => K.indicator Φ x) z, lintegral_indicator hKm]
  have memK : ∀ (c : ℂ) (v : Fin D → ℂ), ‖c‖ = 1 → (z + c • v ∈ K ↔ z + v ∈ K) := by
    intro c v hc
    simp [K, mem_closedBall, dist_eq_norm, norm_smul, hc]
  have hrot : ∀ θ : ℝ, ∫⁻ v, k (circleMap 0 1 θ • v) = ∫⁻ v, k v := fun θ =>
    (smul_mp _ (by simp)).lintegral_comp hkm
  have hθ : ∀ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) ≤
      K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) := by
    intro v
    by_cases hv : z + v ∈ K
    · rw [Set.indicator_of_mem hv]
      have hvt : ‖v‖ ≤ t := by simpa [K, mem_closedBall, dist_eq_norm] using hv
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • v ∈ U := by
        intro ζ hζ
        apply hK
        simp only [K, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
        nlinarith [norm_nonneg ζ, norm_nonneg v]
      obtain ⟨hci, hsub⟩ := hφ.2 z v hdisc
      have hmemθ : ∀ θ : ℝ, z + circleMap 0 1 θ • v ∈ K := fun θ => (memK _ v (by simp)).2 hv
      have hkθ : ∀ θ : ℝ, k (circleMap 0 1 θ • v) =
          ENNReal.ofReal (M - φ (z + circleMap 0 1 θ • v)) := by
        intro θ
        simp only [k, Φ]
        rw [Set.indicator_of_mem (hmemθ θ), hφU _ (hmemθ θ)]
      have hci' : IntegrableOn (fun θ : ℝ => φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hci.1
      have hconst : IntegrableOn (fun _ : ℝ => M) (Ioc 0 (2 * π)) :=
        continuous_const.integrableOn_Ioc
      have hint : IntegrableOn (fun θ : ℝ => M - φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hconst.sub hci'
      rw [lintegral_congr (fun θ => hkθ θ), ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => sub_nonneg.2 (hM _ (hmemθ θ)))]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_sub hconst hci', setIntegral_const]
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul] at hsub
      have hvol : volume.real (Ioc (0:ℝ) (2 * π)) = 2 * π := by
        simp [Real.volume_real_Ioc, two_pi_pos.le]
      rw [hvol, smul_eq_mul]
      have h2 : 0 < 2 * π := two_pi_pos
      have h3 := (le_inv_mul_iff₀ h2).1 hsub
      nlinarith
    · rw [Set.indicator_of_notMem hv]
      have h0 : ∀ θ : ℝ, k (circleMap 0 1 θ • v) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hv ((memK _ v (by simp)).1 h)) _
      simp [h0]
  have hswap : ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) =
      ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) :=
    lintegral_lintegral_swap ((hkm.comp (by fun_prop :
      Continuous fun p : ℝ × (Fin D → ℂ) => circleMap 0 1 p.1 • p.2).measurable).aemeasurable)
  have hmain : ENNReal.ofReal (2 * π) * ∫⁻ v, k v ≤
      ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
    calc ENNReal.ofReal (2 * π) * ∫⁻ v, k v
        = ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) := by
          simp_rw [hrot]
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]
      _ = ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) := hswap
      _ ≤ ∫⁻ v, K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) :=
          lintegral_mono hθ
      _ = ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
          rw [lintegral_add_left_eq_self
            (fun x => K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) x) z,
            lintegral_indicator_const hKm]
  have hbound : ∫⁻ x in K, Φ x ≤ ENNReal.ofReal (M - φ z) * volume K := by
    rw [← hk]
    rw [ENNReal.ofReal_mul two_pi_pos.le, mul_assoc] at hmain
    rw [mul_comm (ENNReal.ofReal (2 * π)), mul_comm (ENNReal.ofReal (2 * π))] at hmain
    exact (ENNReal.mul_le_mul_iff_left (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 hmain
  have hKfin : volume K < ⊤ := measure_closedBall_lt_top
  have hKpos : 0 < volume K := measure_closedBall_pos volume z ht
  have hconstK : IntegrableOn (fun _ : Fin D → ℂ => M) K := continuous_const.continuousOn.integrableOn_compact hKc
  have hψint : IntegrableOn (fun x => M - φU x) K := by
    refine ⟨(measurable_const.sub hφUm).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ x in K, ‖M - φU x‖ₑ = ∫⁻ x in K, Φ x := by
          refine setLIntegral_congr_fun hKm (fun x hx => ?_)
          rw [Real.enorm_of_nonneg (sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))]
      _ ≤ _ := hbound
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin
  have hφint : IntegrableOn φ K := by
    refine (hconstK.sub hψint).congr_fun (fun x hx => ?_) hKm
    simp [hφU x hx]
  refine ⟨hφint, ?_⟩
  have hreal : ∫ x in K, (M - φU x) ≤ (M - φ z) * volume.real K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hKm
      (fun x hx => sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))) hψint.aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (M - φ z) * volume K).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin).ne hbound
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 (hM z hzK))]
          rfl
  have hsplit : ∫ x in K, (M - φU x) = M * volume.real K - ∫ x in K, φ x := by
    rw [integral_sub hconstK (hφint.congr_fun (fun x hx => (hφU x hx).symm) hKm),
      setIntegral_const, smul_eq_mul, mul_comm]
    congr 1
    exact setIntegral_congr_fun hKm (fun x hx => hφU x hx)
  have hKr : 0 < volume.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hKr]
  nlinarith [hreal, hsplit]
end ReciprocityTheory.AnForm.A.PshMean
