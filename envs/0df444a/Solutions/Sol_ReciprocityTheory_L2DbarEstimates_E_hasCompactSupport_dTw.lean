-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_dTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:13.346409+00:00
-- url     : https://prove2.me/submissions/804a8c26-1e40-4545-a61c-0f2b65e4c68e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_tsupport_dTw_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (dTw n z ph j u) := by
  exact hu.mono' ((subset_tsupport _).trans (tsupport_dTw_subset n z ph j u))
end ReciprocityTheory.L2DbarEstimates.E
