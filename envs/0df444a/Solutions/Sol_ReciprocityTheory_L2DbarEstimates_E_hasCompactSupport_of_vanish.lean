-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:25.35181+00:00
-- url     : https://prove2.me/submissions/85a0daf1-1fdd-4288-8793-680c0be4e4ee

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish

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
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (u F : M → ℂ)
    (hu : HasCompactSupport u) (h : ∀ x, u x = 0 → F x = 0) : HasCompactSupport F :=
  hu.mono' fun x hx => subset_tsupport u (mt (h x) hx)
end ReciprocityTheory.L2DbarEstimates.E
