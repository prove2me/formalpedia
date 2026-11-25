-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdA_025f672c8744
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:26.310274+00:00
-- url     : https://prove2.me/submissions/7567c6a6-f5b0-4a70-aa88-828d22f162b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_d_fdddd4d4648e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x₀ : X.A n, Rel (n + 1) X (X.dA n x₀) 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x₀
    refine rel_succ.mpr ⟨X.a 0 x₀, by rw [hX.ha0, map_zero], rel_zero.mpr ?_⟩
    exact hX.a_d 0 x₀
  | succ n ih =>
    intro X hX x₀
    refine rel_succ.mpr ⟨0, by rw [map_zero, map_zero], ?_⟩
    rw [map_zero]
    exact ih X.shift hX.shift x₀
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
