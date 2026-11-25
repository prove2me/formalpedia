-- Prove2me | solution 1 for PI.InvTopW.isOpen_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:31.879473+00:00
-- url     : https://prove2.me/submissions/d81965a0-9404-4910-ad9b-d0fa173a46a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Topology Filter
namespace PI.InvTopW
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    IsOpen ((Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))) :=
  RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
end PI.InvTopW
