-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:28.758488+00:00
-- url     : https://prove2.me/submissions/6bcfb4ad-52c8-4176-80cc-2e98108b8a91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_continuous_pointWithLast_b8f5a1499bb5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0) (a : Fin d → (σ → ℂ) → ℂ)
    (q : (Option σ → ℂ) → ℂ) (hq : AnalyticAt ℂ q 0)
    (h : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = q x * weierstrassPolynomial c x) :
    ∀ j, ∀ᶠ z in 𝓝 (0 : σ → ℂ), a j z = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and hq.eventually_analyticAt)
  have hr0 : 0 < min ε 1 := lt_min hε one_pos
  have hrε : min ε 1 ≤ ε := min_le_left _ _
  have hR : 0 < (min ε 1) ^ d := pow_pos hr0 d
  have hηpos : 0 < (min ε 1) ^ d / (d + 1) := by positivity
  have hη : (d : ℝ) * ((min ε 1) ^ d / (d + 1)) < (min ε 1) ^ d := by
    rw [show (d : ℝ) * ((min ε 1) ^ d / (d + 1)) = (min ε 1) ^ d * (d / (d + 1)) by ring]
    exact mul_lt_of_lt_one_right hR ((div_lt_one (by positivity)).2 (by linarith))
  have hsmall : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ‖z‖ < min ε 1 ∧ ∀ j, ‖c j z‖ ≤ (min ε 1) ^ d / (d + 1) := by
    refine ((continuous_norm.tendsto' (0 : σ → ℂ) 0 norm_zero).eventually (eventually_lt_nhds hr0)).and
      (Filter.eventually_all.2 fun j => ?_)
    have ht : Tendsto (fun z => ‖c j z‖) (𝓝 (0 : σ → ℂ)) (𝓝 0) := by
      simpa [hc0 j] using (hc j).norm.tendsto
    exact (ht.eventually (eventually_lt_nhds hηpos)).mono fun z hz => hz.le
  intro j
  filter_upwards [hsmall] with z hz
  obtain ⟨hzr, hcz⟩ := hz
  have hpt : ∀ t : ℂ, ‖t‖ < min ε 1 → pointWithLast z t ∈ Metric.ball (0 : Option σ → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro o
    cases o with
    | none => exact lt_of_lt_of_le ht hrε
    | some i => exact lt_of_le_of_lt (norm_le_pi_norm z i) (lt_of_lt_of_le hzr hrε)
  have hdeg : (∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := degree_sum_fin_lt _
  have hWm : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).Monic := monic_X_pow_add hdeg
  have hWn : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).natDegree = d := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hevW : ∀ t : ℂ, (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t =
      weierstrassPolynomial c (pointWithLast z t) := by
    intro t
    simp only [eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C, weierstrassPolynomial]
    rfl
  have hevP : ∀ t : ℂ, (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)).eval t =
      ∑ i : Fin d, a i (fun k => pointWithLast z t (some k)) * pointWithLast z t none ^ (i : ℕ) := by
    intro t
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  have hdvd := polynomial_dvd_of_eval_eq_mul_near_roots (Metric.isOpen_ball (x := (0 : ℂ)) (ε := min ε 1)) d
    _ (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) (fun t => q (pointWithLast z t)) hWm hWn
    (fun t ht => ((hball _ (hpt t (mem_ball_zero_iff.1 ht))).2.continuousAt.comp
      (continuous_pointWithLast z).continuousAt).continuousWithinAt)
    (fun t ht => by
      rw [hevP, hevW]
      exact (hball _ (hpt t (mem_ball_zero_iff.1 ht))).1)
    (fun t ht => by
      rw [mem_ball_zero_iff]
      refine norm_lt_of_monic_root_small_coeffs (fun i => c i z) hr0 (min_le_right _ _) hη hcz t ?_
      have h0 : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t = 0 := ht
      simpa only [eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C] using h0)
  have hP0 : (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (by rw [degree_eq_natDegree hWm.ne_zero, hWn]; exact degree_sum_fin_lt _)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (j : ℕ)) hP0
  simpa [finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hcoeff
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
