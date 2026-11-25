-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Asm.mem_fixed_iff_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:01.579126+00:00
-- url     : https://prove2.me/submissions/9114dff2-93c0-43cf-962c-038841d1a2b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_UnitaryHypotheses_ExistsOrthOfFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Asm
namespace PositivityTheory.RgUd.Form.U.Asm
theorem _root_.solution {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp
end PositivityTheory.RgUd.Form.U.Asm
