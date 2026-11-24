-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.span_orbit_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:36.827566+00:00
-- url     : https://prove2.me/submissions/eb83c191-3f1e-4ae8-b25f-ed8ac611c97d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace PositivityTheory.ThKF.Abs
theorem _root_.solution {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) (k : K) :
    ∀ y ∈ Submodule.span ℂ (Set.range fun k => κ k x), κ k y ∈ Submodule.span ℂ (Set.range fun k => κ k x) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => obtain ⟨k', rfl⟩ := h; exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
end PositivityTheory.ThKF.Abs
