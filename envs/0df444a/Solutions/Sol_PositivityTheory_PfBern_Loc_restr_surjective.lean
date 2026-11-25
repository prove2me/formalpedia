-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.restr_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:47.769949+00:00
-- url     : https://prove2.me/submissions/2356292a-f7a0-45e2-a00f-16531840d8ed

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift


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
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution (hZ : IsClosed Z) : Function.Surjective (restr hZ) := by
  intro φ
  obtain ⟨f, hf, hfφ⟩ := exists_lift (U := univ) isOpen_univ (subset_univ Z) φ.2
  exact ⟨⟨f, hf.1⟩, Subtype.ext (funext hfφ)⟩
end PositivityTheory.PfBern.Loc
