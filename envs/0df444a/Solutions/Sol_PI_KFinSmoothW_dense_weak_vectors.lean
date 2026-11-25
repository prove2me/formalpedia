-- Prove2me | solution 1 for PI.KFinSmoothW.dense_weak_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:26.655983+00:00
-- url     : https://prove2.me/submissions/f9c18923-e17a-46c1-ac52-f5b69f315fde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
import Theorems.Thm_PI_KFinSmoothW_umat_mem_UJset
import Theorems.Thm_PI_KFinSmoothW_one_mem_UJset
import Theorems.Thm_PI_KFinSmoothW_gv_sub_norm_le
import Theorems.Thm_PI_KFinSmoothW_qd_contDiff
import Theorems.Thm_PI_KFinSmoothW_qd_one
import Theorems.Thm_PI_KFinSmoothW_qd_conj
import Theorems.Thm_PI_KFinSmoothW_dist_lt_of_qd_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.KFinSmoothW
theorem _root_.solution : StepDenseW := by
  intro n ε H _ _ _ τ hτ W hW

  let R : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] H) := fun g => (τ g).comp W.subtypeL
  have hR : ContinuousWithinAt R (UJset ε) 1 :=
    continuousWithinAt_clm_apply.2 fun y => hτ.2.2 (y : H) 1 one_mem_UJset
  obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.mp hR (1 / 2) (by norm_num)
  have hτ1 : τ 1 = 1 := hτ.1.1
  have hclose : ∀ g ∈ UJset ε, dist g 1 < r → ∀ w ∈ W, ‖τ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hd w hw
    have h1 := hr' hg hd
    rw [dist_eq_norm] at h1
    have h2 := (R g - R 1).le_opNorm ⟨w, hw⟩
    have h3 : (R g - R 1) ⟨w, hw⟩ = τ g w - w := by
      simp [R, hτ1]
    rw [h3] at h2
    have h4 : ‖(⟨w, hw⟩ : W)‖ = ‖w‖ := rfl
    rw [h4] at h2
    calc ‖τ g w - w‖ ≤ ‖R g - R 1‖ * ‖w‖ := h2
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring

  have hr2 : 0 < r ^ 2 := by positivity
  let ψ : ContDiffBump (0 : ℝ) := ⟨r ^ 2 / 2, r ^ 2, half_pos hr2, half_lt_self hr2⟩
  let Φ0 : Matrix (Fin n) (Fin n) ℂ → ℝ := fun x => ψ (qd x)
  have hΦ0c : Continuous Φ0 := ψ.continuous.comp qd_contDiff.continuous
  have hsupp0 : ∀ x, Φ0 x ≠ 0 → dist x 1 < r := by
    intro x hx
    have hb : qd x ∈ Function.support ψ := hx
    rw [ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    exact dist_lt_of_qd_lt hr (lt_of_le_of_lt (le_abs_self _) hb)
  have hcs : HasCompactSupport Φ0 := by
    refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) ?_
    intro x hx
    by_contra hne
    exact hx (Metric.mem_closedBall.2 (hsupp0 x hne).le)
  have hcomp : Continuous (fun h : UJ ε => Φ0 (umat h)) := hΦ0c.comp (continuous_coeMatrix ε)
  have hint : Integrable (fun h : UJ ε => Φ0 (umat h)) (muG ε) :=
    hcomp.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1)
  have hpos : 0 < ∫ h, Φ0 (umat h) ∂(muG ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun h => ψ.nonneg) hint]
    apply IsOpen.measure_pos
    · exact isOpen_ne_fun hcomp continuous_const
    · refine ⟨1, ?_⟩
      show ψ (qd (umat (1 : UJ ε))) ≠ 0
      have h1 : umat (1 : UJ ε) = 1 := rfl
      rw [h1, qd_one, ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]
      exact one_ne_zero
  set c := ∫ h, Φ0 (umat h) ∂(muG ε) with hc
  refine ⟨fun x => ((Φ0 x / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((ψ.contDiff.comp qd_contDiff).div_const c)
  · exact hcs.comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro a ha m
    have hu1 : a * aᴴ = 1 := by
      have := Unitary.mul_star_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    have hu2 : aᴴ * a = 1 := by
      have := Unitary.star_mul_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    simp only [Φ0, qd_conj a m hu1 hu2]
  · intro w hw
    refine gv_sub_norm_le hτ (fun x => Φ0 x / c) (hΦ0c.div_const c)
      (fun x => div_nonneg ψ.nonneg hpos.le) (hint.div_const c)
      (by rw [integral_div, ← hc, div_self hpos.ne']) w (‖w‖ / 2) ?_
    intro h hz
    have hne : Φ0 (umat h) ≠ 0 := by
      intro h0
      apply hz
      show Φ0 (umat h) / c = 0
      rw [h0, zero_div]
    exact hclose _ (umat_mem_UJset h) (hsupp0 _ hne) w hw
end PI.KFinSmoothW
