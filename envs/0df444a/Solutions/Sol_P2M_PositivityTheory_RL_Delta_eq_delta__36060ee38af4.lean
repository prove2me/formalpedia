-- Prove2me | solution 1 for P2M_PositivityTheory_RL_Delta_eq_delta__36060ee38af4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:22.200157+00:00
-- url     : https://prove2.me/submissions/4cfa4215-97c7-434c-b89c-5728a4c41269

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
import Theorems.Thm_PositivityTheory_RL_Delta_eq_delta

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
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]
end PositivityTheory.RL.Delta
