-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.tens_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:37.249246+00:00
-- url     : https://prove2.me/submissions/212a1396-1bfc-48d8-9e0c-1dffdf23cea5

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
theorem _root_.solution {a : Y → ℂ} (ha : a ∈ TF Y) {U : Set W} (hUc : IsCompact U) (hUo : IsOpen U) :
    (fun p : Y × W => a p.1 * U.indicator 1 p.2) ∈ TF (Y × W) := by
  have h1 : IsLocallyConstant (U.indicator (1 : W → ℂ)) :=
    (LocallyConstant.indicator (LocallyConstant.const W (1 : ℂ)) ⟨hUc.isClosed, hUo⟩).isLocallyConstant
  refine ⟨(ha.1.comp_continuous continuous_fst).comp₂ (h1.comp_continuous continuous_snd) (· * ·), ?_⟩
  refine HasCompactSupport.intro (ha.2.isCompact.prod hUc) fun p hp => ?_
  simp only [mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [Set.indicator_of_notMem h]
end PositivityTheory.RgUd.T.Nil.BasePf
