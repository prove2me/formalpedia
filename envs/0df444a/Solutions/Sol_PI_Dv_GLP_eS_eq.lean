-- Prove2me | solution 1 for PI.Dv.GLP.eS_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:13.9261+00:00
-- url     : https://prove2.me/submissions/51bc8ce1-f17f-4004-af15-d266fbb88b84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution (T : GoodSet K G) (s : T.S) :
    eS T s = ∑ x : G, cS T s x • MonoidAlgebra.of K G x := rfl
end PI.Dv.GLP
