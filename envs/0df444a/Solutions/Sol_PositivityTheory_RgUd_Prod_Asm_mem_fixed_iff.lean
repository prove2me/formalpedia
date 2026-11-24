-- Prove2me | solution 1 for PositivityTheory.RgUd.Prod.Asm.mem_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:50.065525+00:00
-- url     : https://prove2.me/submissions/6f58d6b9-1a55-426e-9646-453a45df8a31

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
theorem _root_.solution (K : Subgroup G) (v : V) : v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp
end PositivityTheory.RgUd.Prod.Asm
