-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:44.884301+00:00
-- url     : https://prove2.me/submissions/67396f0b-6c14-4d1a-8875-41476ef50ab3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3


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
theorem _root_.solution (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k)) :
    ∀ g : MvPolynomial (Fin k × Fin n) ℂ, g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ C) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) C)), eval (normT h T u) g ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have e : normT h (∅ : Finset (Fin k)) = id := by funext u ij; simp [normT]
    simp only [e, id]
    exact ⟨integrableOn_log_norm_eval g hg C, ae_eval_ne_zero g hg C⟩
  | insert i T hi ih =>
    intro g hg
    by_cases hhom : ∃ d, IsWeightedHomogeneous (indW (inGroup i)) g d
    · obtain ⟨d, hd⟩ := hhom
      exact logNormT_insert_of_homog h C T i hi g hg d hd (ih g hg).1 (ih g hg).2
    · obtain ⟨m0, hm0⟩ := MvPolynomial.support_nonempty.mpr hg
      set w := indW (inGroup (n := n) i) with hw
      set d0 := Finsupp.weight w m0 with hd0
      set g' := weightedHomogeneousComponent w d0 g with hg'
      have hg'0 : g' ≠ 0 := by
        intro h0
        have := congrArg (coeff m0) h0
        rw [hg', coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
        exact mem_support_iff.mp hm0 this
      obtain ⟨ih1, ih2⟩ := logNormT_insert_of_homog h C T i hi g' hg'0 d0
        (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (ih g' hg'0).1 (ih g' hg'0).2
      obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := Fin k × Fin n) C).exists_bound_of_continuousOn
        (continuous_eval g).continuousOn
      have hD : ∀ m ∈ g.support, Finsupp.weight w m ≤ g.totalDegree :=
        fun m hm => (weight_indW_le _ m).trans (le_totalDegree hm)
      exact circle_lemma volume (polydisc _ C) (measurableSet_polydisc C) (volume_polydisc_ne_top C)
        (fun θ => scaleP (inGroup i) (circleMap 0 1 θ)) (measurable_scaleP _)
        (fun θ => measurePreserving_scaleP _ θ) (fun θ => scale_preimage_polydisc _ θ C)
        (fun u => eval (normT h (insert i T) u) g)
        ((continuous_eval g).measurable.comp (measurable_normT h _))
        (fun d u => eval (normT h (insert i T) u) (weightedHomogeneousComponent w d g))
        g.totalDegree d0 (hD m0 hm0)
        (fun θ u => by
          rw [normT_scaleP]
          exact eval_scaleP _ _ _ g _ hD)
        ih1 ih2 M (fun u hu => hM _ (normT_mem_polydisc h C hC0 hC _ u hu))
end GroundTheory.Heights₂.Heights.LogInt
