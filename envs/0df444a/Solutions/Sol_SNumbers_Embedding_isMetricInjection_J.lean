-- Prove2me | solution 1 for SNumbers.Embedding.isMetricInjection_J
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:18.041398+00:00
-- url     : https://prove2.me/submissions/b9309810-4b69-45e6-8f99-b21842a8f81f

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Embedding
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Embedding
theorem _root_.solution : IsMetricInjection (J : Y →L[𝕜] _) := by
  intro y
  refine le_antisymm ?_ ?_
  · refine lp.norm_le_of_forall_le (norm_nonneg y) fun φ => ?_
    calc ‖(φ : Y →L[𝕜] 𝕜) y‖ ≤ ‖(φ : Y →L[𝕜] 𝕜)‖ * ‖y‖ := (φ : Y →L[𝕜] 𝕜).le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  · obtain ⟨g, hg, hgy⟩ := exists_dual_vector'' 𝕜 y
    have hmem : g ∈ Metric.closedBall (0 : Y →L[𝕜] 𝕜) 1 := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖g y‖ := by rw [hgy, RCLike.norm_ofReal, abs_norm]
      _ = ‖((J : Y →L[𝕜] _) y : DualBall 𝕜 Y → 𝕜) ⟨g, hmem⟩‖ := rfl
      _ ≤ ‖(J : Y →L[𝕜] _) y‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
end SNumbers.Embedding
