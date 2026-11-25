-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.polydisc_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:17.215731+00:00
-- url     : https://prove2.me/submissions/293ba6e9-f222-46f6-bd04-44269d0e6a15

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_cons_mem_ball
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_differentiable_cons
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_disc_mean_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (f : (Fin D → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (w : Fin D → ℝ → ℝ)
    (hwc : ∀ j, Continuous (w j)) (hw : ∀ j s, 0 ≤ w j s) :
    ‖f 0‖ ^ 2 * ∏ j, ∫ z in Metric.ball (0 : ℂ) r, w j ‖z‖ ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * ∏ j, w j ‖z j‖ := by
  induction D with
  | zero =>
    have hb : Metric.ball (0 : Fin 0 → ℂ) r = Set.univ := by
      ext z; simp [Subsingleton.elim z 0, hr]
    rw [hb, Measure.restrict_univ]
    have hc : (fun z : Fin 0 → ℂ => ‖f z‖ ^ 2 * ∏ j, w j ‖z j‖) = fun _ => ‖f 0‖ ^ 2 := by
      funext z; rw [Subsingleton.elim z 0]; simp
    rw [hc]
    rw [volume_pi, integral_const]
    simp [measureReal_def, Measure.pi_empty_univ]
  | succ D ih =>
    have hR : 0 < R := hr.trans hrR
    set B := Metric.ball (0 : ℂ) r with hBdef
    set B' := Metric.ball (0 : Fin D → ℂ) r with hB'def
    set F : (Fin (D + 1) → ℂ) → ℝ := fun z => ‖f z‖ ^ 2 * ∏ j, w j ‖z j‖ with hFdef
    have hFc : ContinuousOn F (Metric.closedBall 0 r) := by
      have h1 : ContinuousOn f (Metric.closedBall 0 r) :=
        hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
      refine (h1.norm.pow 2).mul (continuous_finsetProd _ fun j _ => ?_).continuousOn
      exact (hwc j).comp (continuous_apply j).norm
    have hint : IntegrableOn F (Metric.ball 0 r) :=
      (hFc.integrableOn_compact (isCompact_closedBall 0 r)).mono_set Metric.ball_subset_closedBall
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    have he : MeasurePreserving e.symm
        ((volume : Measure ℂ).prod (volume : Measure (Fin D → ℂ))) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm
    have hes : ∀ p : ℂ × (Fin D → ℂ), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    have hpre : e.symm ⁻¹' Metric.ball 0 r = B ×ˢ B' := by
      ext ⟨x, y⟩
      simp only [Set.mem_preimage, hes, Set.mem_prod, B, B', mem_ball_zero_iff, pi_norm_lt_iff hr,
        Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    have hG : Integrable (fun p : ℂ × (Fin D → ℂ) => F (Fin.cons p.1 p.2))
        ((volume.restrict B).prod (volume.restrict B')) := by
      rw [Measure.prod_restrict, ← hpre]
      have := (he.integrableOn_comp_preimage e.symm.measurableEmbedding).2 hint
      simp only [Function.comp_def, hes] at this
      exact this
    have hI : ∫ z in Metric.ball 0 r, F z = ∫ x in B, ∫ y in B', F (Fin.cons x y) := by
      rw [← he.setIntegral_preimage_emb e.symm.measurableEmbedding, hpre, ← Measure.prod_restrict]
      simp_rw [hes]
      rw [integral_prod _ hG]
    set c := ∏ j : Fin D, ∫ z in B, w j.succ ‖z‖ with hc
    have hc0 : 0 ≤ c :=
      Finset.prod_nonneg fun j _ => setIntegral_nonneg measurableSet_ball fun z _ => hw _ _
    set g : ℂ → ℂ := fun x => f (Fin.cons x 0) with hg
    have hgd : DifferentiableOn ℂ g (Metric.ball 0 R) := by
      refine hf.comp (polydisc_differentiable_cons.comp
        (differentiable_id.prodMk (differentiable_const _))).differentiableOn ?_
      intro x hx
      exact polydisc_cons_mem_ball hR (mem_ball_zero_iff.1 hx) (by simpa using hR)
    have hpt : ∀ x ∈ B, ‖g x‖ ^ 2 * w 0 ‖x‖ * c ≤ ∫ y in B', F (Fin.cons x y) := by
      intro x hx
      have hx' : ‖x‖ < R := (mem_ball_zero_iff.1 hx).trans hrR
      have hfx : DifferentiableOn ℂ (fun y : Fin D → ℂ => f (Fin.cons x y)) (Metric.ball 0 R) := by
        refine hf.comp (polydisc_differentiable_cons.comp
          ((differentiable_const x).prodMk differentiable_id)).differentiableOn ?_
        intro y hy
        exact polydisc_cons_mem_ball hR hx' (mem_ball_zero_iff.1 hy)
      have h := ih (fun y => f (Fin.cons x y)) hfx (fun j => w j.succ) (fun j => hwc _)
        (fun j s => hw _ _)
      have heq : (fun y : Fin D → ℂ => F (Fin.cons x y)) = fun y =>
          w 0 ‖x‖ * (‖f (Fin.cons x y)‖ ^ 2 * ∏ j : Fin D, w j.succ ‖y j‖) := by
        funext y
        simp only [F, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring
      rw [heq, integral_const_mul]
      calc ‖g x‖ ^ 2 * w 0 ‖x‖ * c = w 0 ‖x‖ * (‖f (Fin.cons x 0)‖ ^ 2 * c) := by
            simp only [g]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h (hw _ _)
    have hstep : ∫ x in B, ‖g x‖ ^ 2 * w 0 ‖x‖ * c ≤ ∫ x in B, ∫ y in B', F (Fin.cons x y) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
        hG.integral_prod_left ((ae_restrict_iff' measurableSet_ball).2
          (Filter.Eventually.of_forall hpt))
      exact mul_nonneg (mul_nonneg (by positivity) (hw _ _)) hc0
    have hdisc := disc_mean_le hr hrR g hgd (w 0) (hwc 0) (hw 0)
    have hg0 : g 0 = f 0 := by
      simp only [g]
      congr 1
      ext k
      refine Fin.cases ?_ (fun j => ?_) k <;> simp
    rw [hI, Fin.prod_univ_succ]
    calc ‖f 0‖ ^ 2 * ((∫ z in B, w 0 ‖z‖) * c) = (‖g 0‖ ^ 2 * ∫ z in B, w 0 ‖z‖) * c := by
          rw [hg0]; ring
      _ ≤ (∫ z in B, ‖g z‖ ^ 2 * w 0 ‖z‖) * c := mul_le_mul_of_nonneg_right hdisc hc0
      _ = ∫ x in B, ‖g x‖ ^ 2 * w 0 ‖x‖ * c := (integral_mul_const c _).symm
      _ ≤ _ := hstep
end ReciprocityTheory.GeometryOfNumbersTheory
