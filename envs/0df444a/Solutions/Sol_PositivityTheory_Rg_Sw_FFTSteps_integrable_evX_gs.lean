-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.integrable_evX_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:38.387012+00:00
-- url     : https://prove2.me/submissions/87cca0da-f3bc-4006-9fdf-6d1f34316bf1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_continuous_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_norm_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_gs_half
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_bound_aux
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_sq_le_sum_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (P : PX m n) : ∀ {c : ℝ}, 0 < c → Integrable (fun x => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro c hc
    have e : (fun x => evX (C a : PX m n) x * gs c x) = fun x => a * gs c x := by
      funext x
      simp [evX]
    rw [e]
    exact (integrable_gs hc).const_mul a
  | add p q hp hq =>
    intro c hc
    have e : (fun x => evX (p + q) x * gs c x) = fun x => evX p x * gs c x + evX q x * gs c x := by
      funext x
      simp only [evX, map_add, add_mul]
    rw [e]
    exact (hp hc).add (hq hc)
  | mul_X p k hp =>
    intro c hc
    have hc2 : 0 < c / 2 := by positivity
    have e : (fun x => evX (p * X k) x * gs c x) = fun x =>
        ((if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) * gs (c / 2) x) *
          (evX p x * gs (c / 2) x) := by
      funext x
      simp only [evX, map_mul, eval_X]
      rw [gs_half c x]
      ring
    rw [e]
    refine (hp hc2).bdd_mul (c := 1 + 1 / (c / 2)) ?_ ?_
    · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_gs _))
      by_cases hk : k.2.2 = true
      · simp only [hk, if_true]
        fun_prop
      · simp only [hk, Bool.false_eq_true, if_false]
        fun_prop
    · refine ae_of_all _ fun x => ?_
      have hn : ‖(if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1)‖ = ‖x k.1 k.2.1‖ := by
        split_ifs <;> simp
      rw [norm_mul, norm_gs, hn]
      exact bound_aux hc2 (norm_nonneg _) (sq_le_sum_sum x k.1 k.2.1)
end PositivityTheory.Rg.Sw.FFTSteps
