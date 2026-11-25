-- Prove2me | solution 1 for PositivityTheory.RgUd.Prod.Asm.fixed_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:05.348991+00:00
-- url     : https://prove2.me/submissions/2153c515-b077-4f4b-89c8-116e6ca85102

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
theorem _root_.solution (U C : Subrepresentation ρ) (hUC : U.toSubmodule ⊓ C.toSubmodule = ⊥) (g : G)
    {u c : V} (hu : u ∈ U.toSubmodule) (hc : c ∈ C.toSubmodule) (h : ρ g (u + c) = u + c) :
    ρ g u = u := by
  have h1 : ρ g u - u = c - ρ g c := by
    rw [map_add] at h
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : ρ g u - u ∈ U.toSubmodule ⊓ C.toSubmodule := by
    refine ⟨sub_mem (U.apply_mem_toSubmodule g hu) hu, ?_⟩
    rw [h1]
    exact sub_mem hc (C.apply_mem_toSubmodule g hc)
  rw [hUC] at h2
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h2)
end PositivityTheory.RgUd.Prod.Asm
