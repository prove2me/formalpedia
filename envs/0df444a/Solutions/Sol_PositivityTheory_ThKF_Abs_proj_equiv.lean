-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.proj_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:41.412962+00:00
-- url     : https://prove2.me/submissions/cf4f0f10-7705-4082-8a19-689fbd678d65

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Theorems.Thm_PositivityTheory_ThKF_Abs_orth_stab

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
theorem _root_.solution {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (x : U) :
    Y.starProjection (κ k x) = κ k (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hY _ _ (Y.starProjection_apply_mem x))
  rw [← map_sub]
  exact orth_stab κ hi Y hY k _ (Y.sub_starProjection_mem_orthogonal x)
end PositivityTheory.ThKF.Abs
