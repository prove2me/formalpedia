-- Prove2me | solution 1 for ZetaZeros.D.EllReg.weightedNormLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:18.954917+00:00
-- url     : https://prove2.me/submissions/818e69ca-661c-4fbe-86f5-670b56bd4ba2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
import Theorems.Thm_ZetaZeros_D_EllReg_om_continuous_eps
import Theorems.Thm_ZetaZeros_D_EllReg_om_eps_zero
import Theorems.Thm_ZetaZeros_D_EllReg_om_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution : EpsLimit := by
  unfold EpsLimit
  intro d s M F B hM hF hB
  unfold nrm at hB ⊢
  have he0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : ∀ ξ : E d, Tendsto
      (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop
      (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2)) := by
    intro ξ
    have h1 : Tendsto (fun n : ℕ => om s M (1 / ((n : ℝ) + 1)) ξ) atTop
        (𝓝 (om s 0 0 ξ)) := by
      rw [← om_eps_zero s M ξ]
      exact ((om_continuous_eps s M ξ).tendsto 0).comp he0
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2) atTop
        (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2)) := by
      exact ((ENNReal.continuous_pow 2).tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp h1)
    have hfin : ‖F ξ‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
    exact ENNReal.Tendsto.mul_const h2 (Or.inr hfin)
  have hmeas : ∀ n : ℕ, Measurable fun ξ : E d =>
      ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2 := fun n => by
    have hc := om_continuous (d := d) s M (1 / ((n : ℝ) + 1))
    exact ((ENNReal.measurable_ofReal.comp hc.measurable).pow_const 2).mul
      (hF.measurable.enorm.pow_const 2)
  calc ∫⁻ ξ, ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2
      = ∫⁻ ξ, liminf (fun n : ℕ =>
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ ξ,
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ B := by
        refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hB _ (hpos n) (hle1 n))
end ZetaZeros.D.EllReg
