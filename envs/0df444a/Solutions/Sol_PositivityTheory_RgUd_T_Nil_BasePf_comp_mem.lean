-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:30.909422+00:00
-- url     : https://prove2.me/submissions/1fb64c46-5ec9-4ee2-b700-91cc8e72a998

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
namespace PositivityTheory.RgUd.T.Nil.BasePf
theorem _root_.solution {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (g : G) (hg : Continuous fun w : W => g • w)
    (hg' : Continuous fun w : W => g⁻¹ • w) : (fun p : Y × W => F (p.1, g • p.2)) ∈ TF (Y × W) := by
  refine ⟨hF.1.comp_continuous (continuous_fst.prodMk (hg.comp continuous_snd)), ?_⟩
  refine HasCompactSupport.intro ((hF.2.isCompact).image
    (continuous_fst.prodMk (hg'.comp continuous_snd))) fun x hx => ?_
  by_contra h
  refine hx ⟨(x.1, g • x.2), subset_tsupport _ h, ?_⟩
  all_goals simp
end PositivityTheory.RgUd.T.Nil.BasePf
