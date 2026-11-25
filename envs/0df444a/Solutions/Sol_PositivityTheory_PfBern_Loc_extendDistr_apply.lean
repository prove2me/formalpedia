-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.extendDistr_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:18.112768+00:00
-- url     : https://prove2.me/submissions/1116396b-7d90-4a31-8105-2198050c92af

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
variable {X : Type*} [TopologicalSpace X]
variable {Z : Set X}
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution (hZ : IsClosed Z) (D' : Distr Z) (f : SC X) :
    extendDistr hZ D' f = D' (restr hZ f) :=
  rfl
end PositivityTheory.PfBern.Loc
