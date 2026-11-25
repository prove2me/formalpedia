-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:45.894984+00:00
-- url     : https://prove2.me/submissions/6bfd6218-fab3-439f-b1ce-300e04c7abef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ))
    (v : Fin (k + 1) → ℂ) : sliceDeriv L D v = vecCons (v 0) (L *ᵥ D v) := rfl
end GroundTheory.Heights₂.Heights
