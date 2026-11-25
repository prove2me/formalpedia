-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.eval_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:20.463603+00:00
-- url     : https://prove2.me/submissions/9e77f2a8-657f-4c13-be2e-dae0942f7796

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_actZ_diagonal
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (p : PV ι A B) (hp : IsInv p) (a : ι → ℝ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (actZ (diagonal fun i => cexp (a i)) (diagonal fun i => cexp (-(a i : ℂ))) z) p = eval z p := by
  set F : ℂ → ℂ := fun c => eval (actZ (diagonal fun i => cexp (c * a i))
    (diagonal fun i => cexp (-(c * a i))) z) p with hF
  have hdiff : Differentiable ℂ F := by
    have hF' : F = fun c => eval (Sum.elim (fun x : ι × A => cexp (c * a x.1) * z (Sum.inl x))
        (fun y : ι × B => cexp (-(c * a y.1)) * z (Sum.inr y))) p := by
      funext c
      simp only [hF, actZ_diagonal]
    rw [hF']
    apply differentiable_eval'
    intro v
    rcases v with x | y
    · simp only [Sum.elim_inl]
      fun_prop
    · simp only [Sum.elim_inr]
      fun_prop
  have himag : ∀ t : ℝ, F (I * t) = eval z p := by
    intro t
    have hs : ∀ i, star (cexp (I * t * a i)) = cexp (-(I * t * a i)) := by
      intro i
      rw [show star (cexp (I * t * a i)) = conj (cexp (I * t * a i)) from rfl, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hu : (diagonal fun i => cexp (I * t * a i)) ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [Pi.star_apply, hs i, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hmap : (diagonal fun i => cexp (I * t * a i)).map star =
        diagonal fun i => cexp (-(I * t * a i)) := by
      rw [Matrix.diagonal_map (star_zero _)]
      congr 1
      funext i
      exact hs i
    show eval (actZ (diagonal fun i => cexp (I * t * a i)) (diagonal fun i => cexp (-(I * t * a i))) z) p
      = eval z p
    rw [← hmap]
    exact eval_inv p hp _ hu z
  have hconst : F 1 = eval z p := by
    have han : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hdiff
    have hg : AnalyticOnNhd ℂ (fun _ : ℂ => eval z p) Set.univ := analyticOnNhd_const
    have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = eval z p := by
      have ht : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous (fun t : ℝ => I * (t : ℂ)) := by fun_prop
          have h0 : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simpa [Complex.I_ne_zero] using ht
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => himag t))
    exact han.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (Set.mem_univ 0) hfreq
      (Set.mem_univ 1)
  simpa [hF] using hconst
end PositivityTheory.Rg.Sw.FFTSteps
