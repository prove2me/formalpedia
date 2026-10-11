-- Prove2me | solution 1 for UhlenbeckGauge.integral_trWedge_eq_boundaryChernSimons
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:51:14.369983+00:00
-- url     : https://prove2.me/submissions/94c26497-2314-447f-bb72-64ebb1fa8a76

import Definitions.Def_uhlenbeck_gauge_box_defs
import Theorems.Thm_UhlenbeckGauge_trWedge_curvature_eq_div_chernSimons
open UhlenbeckGauge Matrix MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
private abbrev Smooth {n : ℕ} (f : R4 → Mat n) :=
  ∀ i j, ContDiff ℝ ∞ (fun x => f x i j)
private lemma smooth_pd {n : ℕ} (μ : Fin 4) (f : R4 → Mat n) (hf : Smooth f) :
    Smooth (partialDeriv μ f) := by
  intro i j
  exact ((hf i j).fderiv_right (by simp)).clm_apply contDiff_const
private lemma smooth_mul {n : ℕ} (f g : R4 → Mat n) (hf : Smooth f) (hg : Smooth g) :
    Smooth (fun y => f y * g y) := by
  intro i j
  change ContDiff ℝ ∞ (fun x => ∑ k, f x i k * g x k j)
  exact ContDiff.sum (fun k _ => (hf i k).mul (hg k j))
private lemma smooth_trace {n : ℕ} (f : R4 → Mat n) (hf : Smooth f) :
    ContDiff ℝ ∞ (fun y => trace (f y)) := by
  exact ContDiff.sum (fun i _ => hf i i)
private lemma smooth_current {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (μ : Fin 4) : ContDiff ℝ ∞ (chernSimonsCurrent A μ) := by
  have h : chernSimonsCurrent A μ = fun x => ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ *
      (trace (A x ν * partialDeriv ρ (fun y => A y σ) x) +
        (2 / 3 : ℂ) * trace (A x ν * A x ρ * A x σ)) := by
    funext x
    simp only [chernSimonsCurrent, trace_add, trace_smul, smul_eq_mul]
  rw [h]
  exact ContDiff.sum (fun ν _ => ContDiff.sum (fun ρ _ => ContDiff.sum (fun σ _ =>
    contDiff_const.mul ((smooth_trace _ (smooth_mul _ _ (hA.1 ν)
      (smooth_pd ρ _ (hA.1 σ)))).add (contDiff_const.mul
        (smooth_trace _ (smooth_mul _ _ (smooth_mul _ _ (hA.1 ν) (hA.1 ρ)) (hA.1 σ))))))))
theorem solution {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    ∫ x in Set.Icc a b, trWedge (curvature A x) = boundaryChernSimons a b A := by
  have hK := smooth_current A hA
  have hdiv : Continuous (fun x => ∑ μ : Fin 4,
      fderiv ℝ (chernSimonsCurrent A μ) x (Pi.single μ 1)) := by
    exact (ContDiff.sum (n := ∞) (fun μ _ =>
      ((hK μ).fderiv_right (by simp)).clm_apply contDiff_const)).continuous
  simp_rw [trWedge_curvature_eq_div_chernSimons A hA]
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (chernSimonsCurrent A) (fun μ => fderiv ℝ (chernSimonsCurrent A μ)) ∅ Set.countable_empty
    (fun μ => (hK μ).continuous.continuousOn)
    (fun x _ μ => ((hK μ).differentiable (by simp) x).hasFDerivAt)
    (hdiv.continuousOn.integrableOn_compact isCompact_Icc)
