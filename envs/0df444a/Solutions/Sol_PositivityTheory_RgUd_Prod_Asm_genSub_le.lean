-- Prove2me | solution 1 for PositivityTheory.RgUd.Prod.Asm.genSub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:21.891986+00:00
-- url     : https://prove2.me/submissions/02c6cd34-8083-4717-a5d8-b89a956de5de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Prod PositivityTheory.RgUd.Prod.Asm
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
namespace PositivityTheory.RgUd.Prod.Asm
theorem _root_.solution (M : Submodule ℂ V) (U : Subrepresentation ρ) (h : M ≤ U.toSubmodule) :
    (genSub ρ M).toSubmodule ≤ U.toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨g, x, hx, rfl⟩
  exact U.apply_mem_toSubmodule g (h hx)
end PositivityTheory.RgUd.Prod.Asm
