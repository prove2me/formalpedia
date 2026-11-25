-- Prove2me | solution 1 for ZetaZeros.D.EllReg.convolution_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:05:32.0728+00:00
-- url     : https://prove2.me/submissions/2e8a0b14-382f-476d-98c2-3c740b9eb141

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConvSqLe
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ConvolutionBound
import Theorems.Thm_UpperTheory_Reformulated_B_Qj8_conv_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}
private lemma conv_sq_le (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) (ξ : E d) :
    (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := by
  first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg ξ | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d
private lemma conv_young (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := lintegral_mono fun ξ => conv_sq_le k g hk hg ξ
    _ = (∫⁻ ζ, k ζ) * ∫⁻ ξ, ∫⁻ η, k (ξ - η) * g η ^ 2 :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, ∫⁻ ξ, k (ξ - η) * g η ^ 2 := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by
      congr 1
      refine lintegral_congr fun η => ?_
      rw [lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)),
        lintegral_sub_right_eq_self k η]
    _ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
      rw [lintegral_const_mul _ (hg.pow_const 2)]; ring
private lemma om_measurable (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by
  unfold om; fun_prop
private lemma om_nonneg (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om; positivity
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution : ConvBound := by
  intro d s M ε C N hC hom K F hK hF
  have hKm : Measurable K := hK.measurable
  have hFm : Measurable F := hF.measurable
  obtain ⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ := ⟨_, rfl⟩
  obtain ⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ :=
    ⟨_, rfl⟩
  obtain ⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ := ⟨_, rfl⟩
  obtain ⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ := ⟨_, rfl⟩
  obtain ⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ :=
    ⟨_, rfl⟩
  have hk1 : Measurable k1 := by rw [hk1e]; exact hKm.enorm
  have hk3 : Measurable k3 := by
    rw [hk3e]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm
  have hk2 : Measurable k2 := by rw [hk2e]; exact measurable_const.mul hk3
  have hg1 : Measurable g1 := by
    rw [hg1e]; exact (ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm
  have hg2 : Measurable g2 := by
    rw [hg2e]; exact (ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm
  have hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g →
      Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η) := fun k g hk hg =>
    (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
  have hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η := (hprod k1 g1 hk1 hg1).lintegral_prod_right'
  have hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η := (hprod k2 g2 hk2 hg2).lintegral_prod_right'

  have hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤
      (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := by
    intro ξ
    have h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by
      unfold conv
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun η => ?_
      rw [enorm_mul]
    have hmeas : Measurable fun η => k1 (ξ - η) * g1 η :=
      (hk1.comp (measurable_const.sub measurable_id)).mul hg1
    calc ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ
        ≤ ENNReal.ofReal (om s M ε ξ) * ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η) := by
        refine lintegral_mono fun η => ?_
        have hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η := by
          have h := hom ξ η
          have h' := le_abs_self (om s M ε ξ - om s M ε η)
          linarith
        have hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N := by positivity
        have hY := om_nonneg (s - 1) M ε η
        have he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) +
            ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η)) := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))
        calc ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ)
            ≤ (ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η))) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) := by gcongr
          _ = k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η := by
            rw [hk1e, hk2e, hk3e, hg1e, hg2e]; ring
      _ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _
  have hn : nrm s M ε (conv K F) ≤
      ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ) := by
    unfold nrm
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.rpow_two, ← mul_pow]
    gcongr
    exact hpt ξ
  have hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g →
      (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
    intro k g hk hg
    have h := conv_young k g hk hg
    simp only [← ENNReal.rpow_two] at h ⊢
    calc (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ ζ, k ζ) ^ (2 : ℝ) * ∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  have e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F := by
    unfold nrm; rw [hg1e]; simp only [mul_pow]
  have e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F := by
    unfold nrm; rw [hg2e]; simp only [mul_pow]
  have e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ := by
    rw [hk2e, lintegral_const_mul _ hk3, hk3e]
  have e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ := by rw [hk1e]
  have hMk := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable
    (by norm_num)
  simp only [Pi.add_apply] at hMk
  calc nrm s M ε (conv K F) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hn (by norm_num)
    _ ≤ (∫⁻ ξ, (∫⁻ η, k1 (ξ - η) * g1 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ξ, (∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hMk
    _ ≤ (∫⁻ ζ, k1 ζ) * (∫⁻ η, g1 η ^ 2) ^ (1 / 2 : ℝ) + (∫⁻ ζ, k2 ζ) * (∫⁻ η, g2 η ^ 2) ^ (1 / 2 : ℝ) :=
        add_le_add (hY k1 g1 hk1 hg1) (hY k2 g2 hk2 hg2)
    _ = _ := by rw [e1, e2, e3, e4]
end ZetaZeros.D.EllReg
