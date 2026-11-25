-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:26.51494+00:00
-- url     : https://prove2.me/submissions/a2dbf0fb-e9bc-40a8-9400-a95bd74bb83b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a


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
theorem _root_.solution (h : HermNorm n) (r : ℝ) (i : Fin k) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ => Real.log (h.norm fun j => u (i, j)))
      (polydisc _ r) := by
  classical
  set ℓ : Fin n → MvPolynomial (Fin k × Fin n) ℂ := fun l => ∑ j, MvPolynomial.C (h.mat l j) * X (i, j)
    with hℓdef
  have hℓ : ∀ u l, eval u (ℓ l) = (h.mat *ᵥ fun j => u (i, j)) l := by
    intro u l
    simp [hℓdef, Matrix.mulVec, dotProduct]
  have hℓ0 : ∀ l, ℓ l ≠ 0 := by
    intro l h0
    obtain ⟨j, hj⟩ := h.li_exists_mat_ne_zero l
    have := congrArg (eval (fun ij : Fin k × Fin n => if ij = (i, j) then (1 : ℂ) else 0)) h0
    rw [hℓ, map_zero] at this
    simp [Matrix.mulVec, dotProduct] at this
    exact hj this
  obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := Fin k × Fin n) r).exists_bound_of_continuousOn
    (f := fun u => h.norm fun j => u (i, j))
    (h.li_continuous_norm.comp (continuous_pi fun j => continuous_apply (i, j))).continuousOn
  refine Integrable.mono' (g := fun u => |Real.log (max M 1)| + ∑ l, |Real.log ‖eval u (ℓ l)‖|) ?_
    (Real.measurable_log.comp (measurable_groupNorm h i)).aestronglyMeasurable ?_
  · have : IsFiniteMeasure (volume.restrict (polydisc (Fin k × Fin n) r)) :=
      isFiniteMeasure_restrict.mpr (volume_polydisc_ne_top r)
    exact (integrable_const _).add (integrable_finsetSum _ fun l _ =>
      (integrableOn_log_norm_eval (ℓ l) (hℓ0 l) r).abs)
  · refine (ae_restrict_iff' (measurableSet_polydisc r)).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    set N := h.norm fun j => u (i, j) with hN
    rw [Real.norm_eq_abs]
    have hS : 0 ≤ ∑ l, |Real.log ‖eval u (ℓ l)‖| := by positivity
    by_cases h0 : N = 0
    · rw [h0, Real.log_zero, abs_zero]; positivity
    · have hNpos : 0 < N := lt_of_le_of_ne (h.li_norm_nonneg _) (Ne.symm h0)
      have hup : Real.log N ≤ |Real.log (max M 1)| := by
        refine (Real.log_le_log hNpos ?_).trans (le_abs_self _)
        have := hM u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (h.li_norm_nonneg _)] at this
        exact this.trans (le_max_left _ _)
      have hex : ∃ l, (h.mat *ᵥ fun j => u (i, j)) l ≠ 0 := by
        by_contra hc
        push Not at hc
        apply h0
        rw [hN]
        unfold HermNorm.norm
        simp [hc]
      obtain ⟨l, hl⟩ := hex
      have hlow : -∑ l, |Real.log ‖eval u (ℓ l)‖| ≤ Real.log N := by
        have h1 : Real.log ‖(h.mat *ᵥ fun j => u (i, j)) l‖ ≤ Real.log N :=
          Real.log_le_log (norm_pos_iff.mpr hl) (h.li_norm_mulVec_apply_le _ l)
        have h2 : |Real.log ‖eval u (ℓ l)‖| ≤ ∑ l, |Real.log ‖eval u (ℓ l)‖| :=
          Finset.single_le_sum (f := fun l => |Real.log ‖eval u (ℓ l)‖|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ l)
        rw [hℓ] at h2
        have h3 := neg_abs_le (Real.log ‖(h.mat *ᵥ fun j => u (i, j)) l‖)
        linarith
      rw [abs_le]
      constructor <;> linarith [abs_nonneg (Real.log (max M 1))]
end GroundTheory.Heights₂.Heights.LogInt
