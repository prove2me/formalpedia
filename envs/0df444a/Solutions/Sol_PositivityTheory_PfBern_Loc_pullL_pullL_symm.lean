-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.pullL_pullL_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:31.850801+00:00
-- url     : https://prove2.me/submissions/6da672f3-3150-482f-b5e6-5e019cf10998

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
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution (h : A ≃ₜ B) (f : SC A) : pullL h (pullL h.symm f) = f :=
  Subtype.ext <| funext fun a => by simp [pullL]
end PositivityTheory.PfBern.Loc
