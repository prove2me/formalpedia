-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:44.712163+00:00
-- url     : https://prove2.me/submissions/87bce5e0-2276-4eb5-9bff-89a21e773ae3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
theorem _root_.solution (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ).FG ∧
      Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) : Submodule (𝓞 K) (Unit → K)) :
        Set (Unit → K)) = ⊤ := by
  refine ⟨((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map _).restrictScalars, ?_⟩
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine eq_top_iff.mpr fun v _ => ?_
  have hmem : toOne K x ∈ Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) :
      Submodule (𝓞 K) (Unit → K)) : Set (Unit → K)) :=
    Submodule.subset_span (Submodule.mem_map_of_mem hxJ)
  have hv : v = (v () / x) • toOne K x := by
    funext u
    simp [toOne, div_mul_cancel₀ _ hx0]
  rw [hv]
  exact Submodule.smul_mem _ _ hmem
end GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
