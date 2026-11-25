-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:42.181943+00:00
-- url     : https://prove2.me/submissions/1a199b3a-6191-40f1-a5cf-d795c29a36ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_derivative_eq_sum_2fd815c9f283

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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0)
    (x₀ : Fin n → ℂ)
    (hx₀ : ∀ i, Polynomial.eval (x₀ i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x₀))) ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ V ∩ U, ∀ x' ∈ V ∩ U, ‖x - x'‖ ≤ K * ‖paramMap π x - paramMap π x'‖ := by
  have core : ∀ i, ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ y y' : Fin r → ℂ, ∀ t t' : ℂ,
      dist y (paramMap π x₀) < δ → dist y' (paramMap π x₀) < δ → dist t (x₀ i) < δ →
      dist t' (x₀ i) < δ →
      ∑ k ∈ range ((P i).natDegree + 1), MvPolynomial.eval y ((P i).coeff k) * t ^ k = 0 →
      ∑ k ∈ range ((P i).natDegree + 1), MvPolynomial.eval y' ((P i).coeff k) * t' ^ k = 0 →
      ‖t - t'‖ ≤ K * ‖y - y'‖ := fun i =>
    root_lipschitz_core _ (fun k y => MvPolynomial.eval y ((P i).coeff k)) _ _
      (fun k => MvPolynomial.continuous_eval _)
      (fun k => by
        obtain ⟨L, T, hT, hL⟩ :=
          ((contDiff_eval_mvPolynomial ((P i).coeff k)).contDiffAt (x := paramMap π x₀)).exists_lipschitzOnWith
        exact ⟨L, T, hT, hL⟩)
      (by rw [← eval_map_derivative_eq_sum]; exact hx₀ i)
  choose δ hδ K hK hcore using core
  refine ⟨{x | ∀ i, dist (paramMap π x) (paramMap π x₀) < δ i ∧ dist (x i) (x₀ i) < δ i}, ?_,
    ∑ i, K i, Finset.sum_nonneg fun i _ => hK i, ?_⟩
  · refine Filter.eventually_all.2 fun i => ?_
    exact (((continuous_paramMap π).tendsto x₀).eventually (Metric.ball_mem_nhds _ (hδ i))).and
      (((continuous_apply i).tendsto x₀).eventually (Metric.ball_mem_nhds _ (hδ i)))
  rintro x ⟨hxV, hxU⟩ x' ⟨hxV', hxU'⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hK i) (norm_nonneg _))).2 fun i => ?_
  have h1 := hV x hxV i
  have h2 := hV x' hxV' i
  rw [eval_map_eq_sum] at h1 h2
  have := hcore i _ _ _ _ (hxU i).1 (hxU' i).1 (hxU i).2 (hxU' i).2 h1 h2
  rw [Pi.sub_apply]
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := K) (fun j _ => hK j) (Finset.mem_univ i)
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
