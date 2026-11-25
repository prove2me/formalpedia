-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:53.982539+00:00
-- url     : https://prove2.me/submissions/fd962b9b-33c3-41ae-bee3-8479f8bd2b51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985


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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution [Fintype ι] [DecidableEq ι] (r : ℝ) :
    ∀ (N : ℕ) (g : MvPolynomial ι ℂ), (nonHomog g).card = N → g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro g hN hg
  by_cases h0 : ∀ x, ∃ d, IsWeightedHomogeneous (indW (· = x)) g d
  ·
    obtain ⟨m, hgm, hc⟩ := eq_monomial_of_homog g hg h0
    rw [hgm]
    have hmeas : Measurable fun u : ι → ℂ => Real.log ‖eval u (monomial m (coeff m g))‖ :=
      Real.measurable_log.comp (continuous_eval _).measurable.norm
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (g := fun u => |Real.log ‖coeff m g‖| +
          ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖|) ?_ hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => ?_)
      · have : IsFiniteMeasure (volume.restrict (polydisc ι r)) :=
          isFiniteMeasure_restrict.mpr (volume_polydisc_ne_top r)
        exact (integrable_const _).add (integrable_finsetSum _ fun i _ =>
          ((integrableOn_log_norm_coord r i).abs.const_mul _))
      · rw [Real.norm_eq_abs]
        exact abs_log_eval_monomial_le m _ u
    · have hnull : volume (⋃ i ∈ m.support, {u : ι → ℂ | u i = 0}) = 0 := by
        refine (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun i _ => ?_
        rw [volume_pi]
        exact Measure.pi_hyperplane _ i 0
      have hae : ∀ᵐ u ∂(volume : Measure (ι → ℂ)), u ∉ ⋃ i ∈ m.support, {u : ι → ℂ | u i = 0} :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      refine ae_restrict_of_ae ?_
      filter_upwards [hae] with u hu
      simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hu
      rw [eval_monomial, Finsupp.prod]
      exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hu i hi))
  · push Not at h0
    obtain ⟨x, hx⟩ := h0
    have hxN : x ∈ nonHomog g := by
      simp only [nonHomog, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
      exact hx
    obtain ⟨m0, hm0⟩ := MvPolynomial.support_nonempty.mpr hg
    set w := indW (· = x) with hw
    set d0 := Finsupp.weight w m0 with hd0
    set g' := weightedHomogeneousComponent w d0 g with hg'
    have hg'0 : g' ≠ 0 := by
      intro h
      have := congrArg (coeff m0) h
      rw [hg', coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
      exact mem_support_iff.mp hm0 this
    have hsub : nonHomog g' ⊆ (nonHomog g).erase x := by
      intro y hy
      simp only [nonHomog, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hy ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact hy ⟨d0, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
      · rintro ⟨e, he⟩
        exact hy ⟨e, isWeightedHomogeneous_component_of _ _ g d0 e he⟩
    have hlt : (nonHomog g').card < N := by
      rw [← hN]
      exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hxN)
    obtain ⟨ih1, ih2⟩ := ih _ hlt g' rfl hg'0
    obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := ι) r).exists_bound_of_continuousOn
      (continuous_eval g).continuousOn
    have hD : ∀ m ∈ g.support, Finsupp.weight w m ≤ g.totalDegree :=
      fun m hm => (weight_indW_le _ m).trans (le_totalDegree hm)
    exact circle_lemma volume (polydisc ι r) (measurableSet_polydisc r) (volume_polydisc_ne_top r)
      (fun θ => scaleP (· = x) (circleMap 0 1 θ)) (measurable_scaleP _)
      (fun θ => measurePreserving_scaleP _ θ) (fun θ => scale_preimage_polydisc _ θ r)
      (fun u => eval u g) (continuous_eval g).measurable
      (fun d u => eval u (weightedHomogeneousComponent w d g)) g.totalDegree d0
      (hD m0 hm0) (fun θ u => eval_scaleP _ _ u g _ hD) ih1 ih2 M hM
end GroundTheory.Heights₂.Heights.LogInt
