-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:26.771669+00:00
-- url     : https://prove2.me/submissions/85240f51-b735-489e-bf90-a4fbfc2a8919

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (r : ℝ) (T : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ T) (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) (d : ℕ)
    (hd : IsWeightedHomogeneous (indW (inGroup i)) g d)
    (ih1 : IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ r))
    (ih2 : ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h T u) g ≠ 0) :
    IntegrableOn (fun u => Real.log ‖eval (normT h (insert i T) u) g‖) (polydisc _ r) ∧
      ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h (insert i T) u) g ≠ 0 := by
  have he : ∀ u, eval (normT h (insert i T) u) g =
      (((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹) ^ d * eval (normT h T u) g := by
    intro u
    rw [normT_insert h T i hi, eval_scale_of_isWeightedHomogeneous _ _ _ g d hd]
  simp_rw [he]
  have hmeas : Measurable fun u : Fin k × Fin n → ℂ =>
      Real.log ‖(((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹) ^ d * eval (normT h T u) g‖ :=
    Real.measurable_log.comp (((Complex.measurable_ofReal.comp (measurable_groupNorm h i)).inv.pow_const
      d).mul ((continuous_eval g).measurable.comp (measurable_normT h T))).norm
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (g := fun u => d * |Real.log (h.norm fun j => u (i, j))| +
      |Real.log ‖eval (normT h T u) g‖|) ?_ hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    · exact ((integrableOn_log_groupNorm h r i).abs.const_mul _).add ih1.abs
    · rw [Real.norm_eq_abs]
      exact abs_log_inv_pow_mul_le _ (h.li_norm_nonneg _) d _
  ·
    have hnull : ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)),
        d ≠ 0 → (h.norm fun j => u (i, j)) ≠ 0 := by
      by_cases hd0 : d = 0
      · exact Filter.Eventually.of_forall fun u h' => absurd hd0 h'
      · obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hg
        have hw := hd (mem_support_iff.mp hm)
        rw [weight_indW] at hw
        obtain ⟨ij, hij, hne⟩ : ∃ ij ∈ m.support, (if inGroup i ij then m ij else 0) ≠ 0 := by
          by_contra hc
          push Not at hc
          rw [Finset.sum_eq_zero hc] at hw
          exact hd0 hw.symm
        have hgi : inGroup i ij := by by_contra hc; simp [hc] at hne
        have hnull0 : volume {u : Fin k × Fin n → ℂ | u ij = 0} = 0 := by
          rw [volume_pi]; exact Measure.pi_hyperplane _ ij 0
        refine ae_restrict_of_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull0] with u hu _ h0
        apply hu
        have := congrFun (h.li_eq_zero_of_norm_eq_zero _ h0) ij.2
        simp only [Pi.zero_apply] at this
        have e : (i, ij.2) = ij := by rw [← hgi]
        rw [e] at this
        exact this
    filter_upwards [ih2, hnull] with u hu hn
    refine mul_ne_zero ?_ hu
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr (hn hd0)))
end GroundTheory.Heights₂.Heights.LogInt
