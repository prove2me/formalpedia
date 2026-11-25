-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:30.40226+00:00
-- url     : https://prove2.me/submissions/b160960a-df00-4055-8d09-cd0008db592e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexCharP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights.Targets
namespace InvertibleIndexCharP
theorem _root_.solution {Ω : Type} [Field Ω] (B : Subring Ω) (hp : ringChar Ω ≠ 0)
    (hB : Module.Finite ℤ B) : Finite B := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ringChar Ω : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩
  rw [Submonoid.smul_def]
  ext
  simp [zsmul_eq_mul]
end InvertibleIndexCharP
end GroundTheory.Heights₂.Heights.Targets
