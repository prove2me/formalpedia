-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:15.375827+00:00
-- url     : https://prove2.me/submissions/21b45210-ed9f-4fe4-b351-2f58e3993a49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {ι : Type*} [Fintype ι] (v : ι → V) (y : V) :
    ‖y - (Submodule.span ℂ (Set.range v)).starProjection y‖ ≤ ‖y‖ := by
  set U := Submodule.span ℂ (Set.range v)
  calc ‖y - U.starProjection y‖ ≤ ‖y - ((0 : U) : V)‖ := by
        rw [Submodule.starProjection_minimal]
        exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (0 : U)
    _ = ‖y‖ := by simp
end GroundTheory.Heights₂.Heights.LatticeLemmas
