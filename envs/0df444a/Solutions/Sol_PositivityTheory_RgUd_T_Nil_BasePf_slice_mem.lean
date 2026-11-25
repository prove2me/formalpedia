-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.slice_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:32.800859+00:00
-- url     : https://prove2.me/submissions/34b02081-3a40-4564-b8b5-b501660a1de0

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
theorem _root_.solution {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (w : W) : (fun y => F (y, w)) ∈ TF Y := by
  refine ⟨hF.1.comp_continuous (continuous_id.prodMk continuous_const), ?_⟩
  refine HasCompactSupport.intro (hF.2.isCompact.image continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, w), subset_tsupport _ h, rfl⟩
end PositivityTheory.RgUd.T.Nil.BasePf
