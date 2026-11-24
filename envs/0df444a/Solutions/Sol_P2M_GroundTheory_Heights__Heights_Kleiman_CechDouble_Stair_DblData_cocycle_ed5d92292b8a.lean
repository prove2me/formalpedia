-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_cocycle_ed5d92292b8a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:06.550428+00:00
-- url     : https://prove2.me/submissions/082249a8-400d-4b03-a826-5e66633db73f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_d_fdddd4d4648e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_injective_237f2d3278a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_injective_5ccb4502175c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_vc0_3c2fabe2c488

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
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x y, Rel n X x y → X.dA n x = 0 ∧ X.dC n y = 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x y hr
    have hr' := rel_zero.mp hr
    refine ⟨hX.a_injective 1 ?_, hX.c_injective 1 ?_⟩
    · rw [hX.a_d, hr', hX.vc0, map_zero]
    · rw [hX.c_d, ← hr', hX.ha0, map_zero]
  | succ n ih =>
    intro X hX x y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    refine ⟨(ih X.shift hX.shift x (X.up n z) hr).1, hX.c_injective (n + 2) ?_⟩
    rw [hX.c_d, ← hz, hX.hh, map_zero]
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
