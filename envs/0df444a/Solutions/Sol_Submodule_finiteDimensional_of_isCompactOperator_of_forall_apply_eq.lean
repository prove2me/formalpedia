-- Prove2me | solution 1 for Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8ef8e514-a8e3-5fa6-b3f7-8fe2c06bfbd2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq

set_option autoImplicit false
open Topology

theorem solution
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V := by

  let W : Submodule 𝕜 E := LinearMap.ker ((T : E →ₗ[𝕜] E) - LinearMap.id)
  have hWmem : ∀ v : E, v ∈ W ↔ T v = v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hVW : V ≤ W := fun v hv => (hWmem v).mpr (hV v hv)
  have hWclosed : IsClosed (W : Set E) := by
    have : (W : Set E) = {v | T v = v} := Set.ext fun v => hWmem v
    rw [this]
    exact isClosed_eq T.continuous continuous_id

  haveI : FiniteDimensional 𝕜 ↥W := by
    refine FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one ?_
    have hK : IsCompact (closure ((T : E → E) '' Metric.closedBall 0 1)) := by
      have h := hT.isCompact_closure_image_ball (f := (T : E →ₗ[𝕜] E)) 2
      exact h.of_isClosed_subset isClosed_closure
        (closure_mono (Set.image_mono (Metric.closedBall_subset_ball (by norm_num))))
    have hemb : Topology.IsClosedEmbedding (Subtype.val : ↥W → E) :=
      hWclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hK.of_isClosed_subset (hemb.isClosedMap _ Metric.isClosed_closedBall) ?_
    rintro _ ⟨w, hw, rfl⟩
    refine subset_closure ⟨(w : E), ?_, ((hWmem w).mp w.2)⟩
    simpa using hw
  exact Submodule.finiteDimensional_of_le hVW

end S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq
end P2MW
export P2MW.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq (solution)
