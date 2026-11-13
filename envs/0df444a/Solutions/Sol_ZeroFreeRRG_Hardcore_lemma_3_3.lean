-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:27:33.219866+00:00
-- url     : https://prove2.me/submissions/76b6d68c-2507-4315-9dfa-59be25197730

import Mathlib
import Theorems.Thm_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap
open Set Metric MeasureTheory

private lemma compact_uniform_closedBall (K L : Set ℂ) (hK : IsCompact K)
    (hKL : K ⊆ interior L) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, closedBall z r ⊆ L := by
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open isOpen_interior hKL
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact (Metric.closedBall_subset_cthickening hz r).trans (hsub.trans interior_subset)

private lemma holomorphic_disk_integral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) :
    ∫ z in ball c R, f z = (Real.pi * R^2) • f c := by
  have hcont : ContinuousOn f (closedBall c R) := hf.continuousOn
  have hint : IntegrableOn f (ball c R) :=
    (hcont.integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  rw [Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap hint]
  have hinner : ∀ r ∈ Ioo (0:ℝ) R, (∫ θ in (0:ℝ)..2*Real.pi, f (circleMap c r θ)) =
      (2 * Real.pi) • f c := by
    intro r hr
    have hclosed : closedBall c |r| ⊆ closedBall c R :=
      closedBall_subset_closedBall (by rw [abs_of_pos hr.1]; exact hr.2.le)
    have hdiff : DiffContOnCl ℂ f (ball c |r|) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c (abs_ne_zero.mpr (ne_of_gt hr.1))]
      exact hf.mono hclosed
    have havg := hdiff.circleAverage
    rw [Real.circleAverage_def] at havg
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    calc
      (∫ θ in (0:ℝ)..2*Real.pi, f (circleMap c r θ)) =
          (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2*Real.pi, f (circleMap c r θ)) := by
            rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
      _ = (2 * Real.pi) • f c := by rw [havg]
  calc
    (∫ r in Ioo (0:ℝ) R, r • ∫ θ in (0:ℝ)..2*Real.pi, f (circleMap c r θ)) =
        ∫ r in Ioo (0:ℝ) R, r • ((2*Real.pi) • f c) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro r hr
          simp only
          rw [hinner r hr]
    _ = (∫ r in Ioo (0:ℝ) R, r) • ((2*Real.pi) • f c) := integral_smul_const _ _
    _ = (Real.pi * R^2) • f c := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le, integral_id]
      rw [smul_smul]
      congr 1
      ring

theorem solution (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (K L : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L) (hLD : L ⊆ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℂ → ℂ, DifferentiableOn ℂ h D →
      ∀ z ∈ K, ‖h z‖ ^ 2 ≤ C * ∫ w in L, ‖h w‖ ^ 2 := by
  obtain ⟨r, hr, hrsub⟩ := compact_uniform_closedBall K L hK hKL
  have hc : 0 < Real.pi * r^2 := by positivity
  refine ⟨(Real.pi * r^2)⁻¹, inv_pos.mpr hc, ?_⟩
  intro h hh z hz
  have hdiff : DifferentiableOn ℂ (fun z => h z ^ 2) (closedBall z r) :=
    (hh.mono ((hrsub z hz).trans hLD)).pow 2
  have heq := holomorphic_disk_integral (fun z => h z ^ 2) z r hr hdiff
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict (ball z r))
    (fun z => h z ^ 2)
  rw [heq, norm_smul, Real.norm_of_nonneg hc.le, norm_pow] at hnorm
  simp only [norm_pow] at hnorm
  have hcont : ContinuousOn (fun z => ‖h z‖ ^ 2) L :=
    ((hh.mono hLD).continuousOn.norm).pow 2
  have hint : IntegrableOn (fun z => ‖h z‖ ^ 2) L := hcont.integrableOn_compact hL
  have hmono : (∫ w in ball z r, ‖h w‖ ^ 2) ≤ ∫ w in L, ‖h w‖ ^ 2 := by
    apply setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    · exact Filter.Eventually.of_forall (fun _ hw => (hrsub z hz) (ball_subset_closedBall hw))
  have hfinal : (Real.pi * r^2) * ‖h z‖ ^ 2 ≤ ∫ w in L, ‖h w‖ ^ 2 := by
    exact hnorm.trans hmono
  exact (le_inv_mul_iff₀ hc).2 hfinal

