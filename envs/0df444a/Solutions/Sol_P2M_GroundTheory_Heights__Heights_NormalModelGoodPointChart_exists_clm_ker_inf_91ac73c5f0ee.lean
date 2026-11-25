-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:10.267806+00:00
-- url     : https://prove2.me/submissions/ef5dad72-3454-4d24-86bf-17a04fa97f7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
open MvPolynomial Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F) (hL : Function.Surjective L) (d : ℕ)
    (hd : Module.finrank ℂ E = d + Module.finrank ℂ F) :
    ∃ A : E →L[ℂ] (Fin d → ℂ), ∀ v, A v = 0 → L v = 0 → v = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.ker L).exists_isCompl
  have hdK : Module.finrank ℂ (LinearMap.ker L) = d := by
    have := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hL, finrank_top] at this
    omega
  let eK : LinearMap.ker L ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ (Fin d → ℂ) (by simp [hdK])
  refine ⟨LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto q hq),
    fun v hA hLv => ?_⟩
  have h2 : v ∈ LinearMap.ker L := LinearMap.mem_ker.2 hLv
  have h3 : (LinearMap.ker L).projectionOnto q hq v = 0 := eK.injective (by simpa using hA)
  rw [Submodule.projectionOnto_apply_of_mem_left hq h2] at h3
  simpa using congrArg Subtype.val h3
end GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
