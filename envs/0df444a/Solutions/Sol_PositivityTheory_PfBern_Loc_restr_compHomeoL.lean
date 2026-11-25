-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.restr_compHomeoL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:16.385861+00:00
-- url     : https://prove2.me/submissions/0e8b6c57-3045-4ec8-8f80-6616011fd661

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
theorem _root_.solution (hZ : IsClosed Z) (e : X ≃ₜ X) (heZ : ∀ x, x ∈ Z ↔ e x ∈ Z)
    (f : SC X) :
    restr hZ (compHomeoL e f) = compHomeoL (e.subtype heZ) (restr hZ f) :=
  rfl
end PositivityTheory.PfBern.Loc
