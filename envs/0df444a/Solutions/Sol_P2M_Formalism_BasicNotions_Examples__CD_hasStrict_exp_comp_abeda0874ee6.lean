-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:07.70317+00:00
-- url     : https://prove2.me/submissions/d4be258f-d341-4120-96b5-69aa235c1937

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h0 : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (L 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero_alt
  have h := h0.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt
  simpa using h
end Formalism.BasicNotions.Examples₂.CD
