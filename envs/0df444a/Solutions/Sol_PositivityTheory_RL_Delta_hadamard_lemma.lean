-- Prove2me | solution 1 for PositivityTheory.RL.Delta.hadamard_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:34.424152+00:00
-- url     : https://prove2.me/submissions/847aed0f-5e97-4cc7-a6e3-4e9a024f0929

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff
namespace PositivityTheory.RL.Delta
theorem _root_.solution : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x := by
  intro n f hf h0
  have hD : ∀ v : Fin n → ℝ, ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) := fun v =>
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hmean : ∀ h : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ h →
      ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∫ s in (0 : ℝ)..1, h (s • x)) := by
    intro h hh
    let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    have hk : IsCompact (Metric.closedBall (0 : ℝ) 2) := isCompact_closedBall _ _
    have hloc : MeasureTheory.LocallyIntegrable
        ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) MeasureTheory.volume :=
      (MeasureTheory.locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioc
    have hsm : ContDiffOn ℝ ∞ (Function.uncurry fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p))
        (Set.univ ×ˢ Set.univ) := by
      refine ContDiff.contDiffOn ?_
      exact (b.contDiff.comp contDiff_snd).smul (hh.comp (contDiff_snd.neg.smul contDiff_fst))
    have key := MeasureTheory.contDiffOn_convolution_right_with_param_comp (n := (⊤ : ℕ∞))
      (μ := MeasureTheory.volume) (ContinuousLinearMap.lsmul ℝ ℝ) (s := Set.univ)
      (v := fun _ : Fin n → ℝ => (0 : ℝ)) contDiffOn_const
      (g := fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p)) isOpen_univ hk
      (fun p t _ ht => by
        have : b t = 0 := image_eq_zero_of_notMem_tsupport (by rw [b.tsupport_eq]; exact ht)
        simp [this]) hloc hsm
    rw [contDiffOn_univ] at key
    convert key using 2 with x
    rw [MeasureTheory.convolution_def, intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : b (-t) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, norm_neg, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2)
      simp [ht, this]
    · simp [ht]
  refine ⟨fun i x => ∫ s in (0 : ℝ)..1, fderiv ℝ f (s • x) (Pi.single i 1),
    fun i => hmean _ (hD _), fun x => ?_⟩
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (s • x) x) s := by
    intro s _
    have := (hd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
    rw [one_smul] at this
    exact this
  have hcv : ∀ v : Fin n → ℝ, Continuous (fun s : ℝ => fderiv ℝ f (s • x) v) := fun v =>
    (hD v).continuous.comp (continuous_id.smul continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcv x).intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, h0, sub_zero] at hftc
  rw [← hftc]
  have hx : ∀ s : ℝ, fderiv ℝ f (s • x) x =
      ∑ i, (x i : ℂ) * fderiv ℝ f (s • x) (Pi.single i 1) := by
    intro s
    calc fderiv ℝ f (s • x) x = fderiv ℝ f (s • x) (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) :=
          congrArg (fderiv ℝ f (s • x)) (pi_eq_sum_univ' x)
      _ = _ := by simp only [map_sum, map_smul, Complex.real_smul]
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · exact fun i _ => (continuous_const.mul (hcv _)).intervalIntegrable 0 1
end PositivityTheory.RL.Delta
